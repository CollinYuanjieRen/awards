import MerLeanExperiment.Certificates.B16_2_2.Steps0700_0799

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1184 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1087, some c1180, some c1183, some c194, some c193, some c119, some c1179, some c1175, some c22, some c167, some c78, some c1176, some c1008, some c381, some c185, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 57) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1127, c1087, c1180, c1183, c194, c193, c119, c1179, c1175, c22, c167, c78, c1176, c1008, c381, c185] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1180 := derived1180 a h
  have h3 : Entails.eval a c1183 := derived1183 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c1179 := derived1179 a h
  have h8 : Entails.eval a c1175 := derived1175 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c1176 := derived1176 a h
  have h13 : Entails.eval a c1008 := derived1008 a h
  have h14 : Entails.eval a c381 := h 380 (by decide)
  have h15 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1184, some c1087, some c107, some c1181, some c1005, some c22, some c10, some c1094, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 57) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c1184, c1087, c107, c1181, c1005, c22, c10, c1094] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1181 := derived1181 a h
  have h4 : Entails.eval a c1005 := derived1005 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c1094 := derived1094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c15, some c1094, some c22, some c8, some c193, some c1087, some c377, some c378, some c1170, some c1008, some c184, some c196, some c19, some c1102, some c300, some c198, some c62, some c339, some c157, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 57) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c194, c15, c1094, c22, c8, c193, c1087, c377, c378, c1170, c1008, c184, c196, c19, c1102, c300, c198, c62, c339, c157] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c1094 := derived1094 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c1087 := derived1087 a h
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c1170 := derived1170 a h
  have h10 : Entails.eval a c1008 := derived1008 a h
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c1102 := derived1102 a h
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c62 := h 61 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1185, some c1186, some c194, some c15, some c1094, some c22, some c193, some c1184, some c1127, some c179, some c1, some c1008, some c105, some c1170, some c356, some c19, some c1171, some c122, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 57) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c1185, c1186, c194, c15, c1094, c22, c193, c1184, c1127, c179, c1, c1008, c105, c1170, c356, c19, c1171, c122] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c1185 := derived1185 a h
  have h1 : Entails.eval a c1186 := derived1186 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c1094 := derived1094 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c1184 := derived1184 a h
  have h8 : Entails.eval a c1127 := derived1127 a h
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c1008 := derived1008 a h
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c1170 := derived1170 a h
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c1171 := derived1171 a h
  have h17 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c1185, some c15, some c8, some c1094, some c1187, some c114, some c229, some c162, some c78, some c589, some c255, some c381, some c360, some c28, some c370, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 57) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c194, c1185, c15, c8, c1094, c1187, c114, c229, c162, c78, c589, c255, c381, c360, c28, c370] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c1185 := derived1185 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c1094 := derived1094 a h
  have h5 : Entails.eval a c1187 := derived1187 a h
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c589 := derived589 a h
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c381 := h 380 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c193, some c194, some c1184, some c1127, some c1087, some c1188, some c26, some c34, some c167, some c22, some c1099, some c15, some c1186, some c122, some c861, some c19, some c105, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 57) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c193, c194, c1184, c1127, c1087, c1188, c26, c34, c167, c22, c1099, c15, c1186, c122, c861, c19, c105] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c193 := h 192 (by decide)
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1127 := derived1127 a h
  have h4 : Entails.eval a c1087 := derived1087 a h
  have h5 : Entails.eval a c1188 := derived1188 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c1099 := derived1099 a h
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c1186 := derived1186 a h
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c861 := derived861 a h
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1184, some c1127, some c194, some c1189, some c119, some c26, some c34, some c167, some c264, some c263, some c117, some c3, some c15, some c250, some c245, some c107, some c359, some c10, some c1158, some c1010, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 57) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c1184, c1127, c194, c1189, c119, c26, c34, c167, c264, c263, c117, c3, c15, c250, c245, c107, c359, c10, c1158, c1010] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1127 := derived1127 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c1189 := derived1189 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c107 := h 106 (by decide)
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c1158 := derived1158 a h
  have h19 : Entails.eval a c1010 := derived1010 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1190, some c14, some c192, some c6, some c1184, some c1127, some c921, some c117, some c34, some c23, some c262, some c261, some c165, some c35, some c107, some c30, some c1041, some c257, some c1, some c94, some c1158, some c113, some c359, some c1003, some c18, some c382, some c1090, some c972, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 57) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c1190, c14, c192, c6, c1184, c1127, c921, c117, c34, c23, c262, c261, c165, c35, c107, c30, c1041, c257, c1, c94, c1158, c113, c359, c1003, c18, c382, c1090, c972] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c1190 := derived1190 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c1184 := derived1184 a h
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c921 := derived921 a h
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c1041 := derived1041 a h
  have h17 : Entails.eval a c257 := h 256 (by decide)
  have h18 : Entails.eval a c1 := h 0 (by decide)
  have h19 : Entails.eval a c94 := h 93 (by decide)
  have h20 : Entails.eval a c1158 := derived1158 a h
  have h21 : Entails.eval a c113 := h 112 (by decide)
  have h22 : Entails.eval a c359 := h 358 (by decide)
  have h23 : Entails.eval a c1003 := derived1003 a h
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c382 := h 381 (by decide)
  have h26 : Entails.eval a c1090 := derived1090 a h
  have h27 : Entails.eval a c972 := derived972 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1190, some c14, some c192, some c6, some c1127, some c1087, some c30, some c1041, some c1, some c113, some c191, some c18, some c1097, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 57) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c1190, c14, c192, c6, c1127, c1087, c30, c1041, c1, c113, c191, c18, c1097] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c1190 := derived1190 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1087 := derived1087 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1041 := derived1041 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c1097 := derived1097 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1184, some c107, some c1191, some c1190, some c14, some c192, some c6, some c1127, some c1087, some c22, some c1099, some c1192, some c264, some c122, some c233, some c18, some c1097, some c171, some c1014, some c176, some c82, some c250, some c1166, some c368, some c381, some c366, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 57) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c1184, c107, c1191, c1190, c14, c192, c6, c1127, c1087, c22, c1099, c1192, c264, c122, c233, c18, c1097, c171, c1014, c176, c82, c250, c1166, c368, c381, c366] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1191 := derived1191 a h
  have h3 : Entails.eval a c1190 := derived1190 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c1127 := derived1127 a h
  have h8 : Entails.eval a c1087 := derived1087 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c1099 := derived1099 a h
  have h11 : Entails.eval a c1192 := derived1192 a h
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c233 := h 232 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c1097 := derived1097 a h
  have h17 : Entails.eval a c171 := h 170 (by decide)
  have h18 : Entails.eval a c1014 := derived1014 a h
  have h19 : Entails.eval a c176 := h 175 (by decide)
  have h20 : Entails.eval a c82 := h 81 (by decide)
  have h21 : Entails.eval a c250 := h 249 (by decide)
  have h22 : Entails.eval a c1166 := derived1166 a h
  have h23 : Entails.eval a c368 := h 367 (by decide)
  have h24 : Entails.eval a c381 := h 380 (by decide)
  have h25 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1194 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1190, some c14, some c6, some c1184, some c1127, some c107, some c1193, some c165, some c23, some c75, some c86, some c82, some c264, some c263, some c250, some c373, some c372, some c236, some c475, some c368, some c255, some c366, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 57) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c1190, c14, c6, c1184, c1127, c107, c1193, c165, c23, c75, c86, c82, c264, c263, c250, c373, c372, c236, c475, c368, c255, c366] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c1190 := derived1190 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c1184 := derived1184 a h
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c1193 := derived1193 a h
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c250 := h 249 (by decide)
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c236 := h 235 (by decide)
  have h18 : Entails.eval a c475 := derived475 a h
  have h19 : Entails.eval a c368 := h 367 (by decide)
  have h20 : Entails.eval a c255 := h 254 (by decide)
  have h21 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1195 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c87, some c86, some c82, some c369, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 57) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c87, c86, c82, c369] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c87 := h 86 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1190, some c14, some c165, some c1191, some c192, some c1127, some c1087, some c264, some c122, some c18, some c1097, some c171, some c233, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 57) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c1190, c14, c165, c1191, c192, c1127, c1087, c264, c122, c18, c1097, c171, c233] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c1190 := derived1190 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c1191 := derived1191 a h
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c1087 := derived1087 a h
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c1097 := derived1097 a h
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1194, some c1195, some c1196, some c30, some c35, some c258, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 57) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c1194, c1195, c1196, c30, c35, c258] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c1194 := derived1194 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c1196 := derived1196 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1198 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1191, some c1190, some c14, some c1184, some c1127, some c1194, some c1197, some c105, some c18, some c122, some c23, some c35, some c165, some c170, some c258, some c1143, some c90, some c229, some c369, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 57) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c1191, c1190, c14, c1184, c1127, c1194, c1197, c105, c18, c122, c23, c35, c165, c170, c258, c1143, c90, c229, c369] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c1191 := derived1191 a h
  have h1 : Entails.eval a c1190 := derived1190 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c1184 := derived1184 a h
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1194 := derived1194 a h
  have h6 : Entails.eval a c1197 := derived1197 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c258 := h 257 (by decide)
  have h15 : Entails.eval a c1143 := derived1143 a h
  have h16 : Entails.eval a c90 := h 89 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1199 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1087, some c1184, some c1190, some c6, some c14, some c192, some c1198, some c26, some c34, some c264, some c263, some c122, some c1196, some c18, some c75, some c105, some c1097, some c250, some c1195, some c82, some c1193, some c369, some c372, some c236, some c368, some c163, some c366, some c1, some c377, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 57) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c1127, c1087, c1184, c1190, c6, c14, c192, c1198, c26, c34, c264, c263, c122, c1196, c18, c75, c105, c1097, c250, c1195, c82, c1193, c369, c372, c236, c368, c163, c366, c1, c377] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1190 := derived1190 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c1198 := derived1198 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c1196 := derived1196 a h
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c1097 := derived1097 a h
  have h18 : Entails.eval a c250 := h 249 (by decide)
  have h19 : Entails.eval a c1195 := derived1195 a h
  have h20 : Entails.eval a c82 := h 81 (by decide)
  have h21 : Entails.eval a c1193 := derived1193 a h
  have h22 : Entails.eval a c369 := h 368 (by decide)
  have h23 : Entails.eval a c372 := h 371 (by decide)
  have h24 : Entails.eval a c236 := h 235 (by decide)
  have h25 : Entails.eval a c368 := h 367 (by decide)
  have h26 : Entails.eval a c163 := h 162 (by decide)
  have h27 : Entails.eval a c366 := h 365 (by decide)
  have h28 : Entails.eval a c1 := h 0 (by decide)
  have h29 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨46, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c117, some c122, some c22, some c18, some c167, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 57) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c1087, c1199, c108, c111, c1127, c117, c122, c22, c18, c167] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1201 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c111, some c1127, some c113, some c1, some c241, some c471, some c628, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 57) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c1087, c1199, c111, c1127, c113, c1, c241, c471, c628] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1127 := derived1127 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c471 := derived471 a h
  have h8 : Entails.eval a c628 := derived628 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c224, some c203, some c65, some c51, some c131, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 57) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c224, c203, c65, c51, c131] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c224 := h 223 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1203 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1202, some c67, some c131, some c49, some c51, some c212, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 57) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c1202, c67, c131, c49, c51, c212] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c1202 := derived1202 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1204 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c263, some c264, some c1199, some c1087, some c26, some c40, some c1200, some c1203, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 57) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c1127, c263, c264, c1199, c1087, c26, c40, c1200, c1203] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c1087 := derived1087 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c1200 := derived1200 a h
  have h8 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1205 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1204, some c1127, some c264, some c1087, some c1199, some c108, some c1006, some c33, some c6, some c247, some c97, some c471, some c93, some c376, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 57) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c1204, c1127, c264, c1087, c1199, c108, c1006, c33, c6, c247, c97, c471, c93, c376] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c1204 := derived1204 a h
  have h1 : Entails.eval a c1127 := derived1127 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c1199 := derived1199 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1006 := derived1006 a h
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c471 := derived471 a h
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1206 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c264, some c263, some c1204, some c1205, some c1203, some c117, some c122, some c1200, some c29, some c18, some c78, some c114, some c242, some c1, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 57) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c1087, c1199, c108, c111, c1127, c264, c263, c1204, c1205, c1203, c117, c122, c1200, c29, c18, c78, c114, c242, c1] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c1204 := derived1204 a h
  have h8 : Entails.eval a c1205 := derived1205 a h
  have h9 : Entails.eval a c1203 := derived1203 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c1200 := derived1200 a h
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c78 := h 77 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c242 := h 241 (by decide)
  have h18 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1207 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c1005, some c119, some c1, some c29, some c241, some c242, some c102, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 57) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c1087, c1199, c108, c111, c1127, c1005, c119, c1, c29, c241, c242, c102] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1005 := derived1005 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c242 := h 241 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1208 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c22, some c29, some c1201, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 57) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c1087, c1199, c108, c22, c29, c1201] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c1201 := derived1201 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1209 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c1206, some c1087, some c1199, some c108, some c111, some c1207, some c6, some c18, some c196, some c1208, some c247, some c262, some c471, some c74, some c93, some c235, some c376, some c168, some c184, some c594, some c665, some c72, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1209 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 57) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c192, c1206, c1087, c1199, c108, c111, c1207, c6, c18, c196, c1208, c247, c262, c471, c74, c93, c235, c376, c168, c184, c594, c665, c72] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c1206 := derived1206 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c1207 := derived1207 a h
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c1208 := derived1208 a h
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c262 := h 261 (by decide)
  have h13 : Entails.eval a c471 := derived471 a h
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  have h16 : Entails.eval a c235 := h 234 (by decide)
  have h17 : Entails.eval a c376 := h 375 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c184 := h 183 (by decide)
  have h20 : Entails.eval a c594 := derived594 a h
  have h21 : Entails.eval a c665 := derived665 a h
  have h22 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1210 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1201, some c372, some c21, some c1141, some c317, some c344, some c219, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1210 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 57) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c1201, c372, c21, c1141, c317, c344, c219] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c1201 := derived1201 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c1141 := derived1141 a h
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1211 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c1087, some c1199, some c108, some c111, some c6, some c18, some c196, some c1210, some c74, some c84, some c81, some c380, some c381, some c161, some c369, some c317, some c364, some c151, some c328, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1211 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 57) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c192, c1087, c1199, c108, c111, c6, c18, c196, c1210, c74, c84, c81, c380, c381, c161, c369, c317, c364, c151, c328] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1199 := derived1199 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c1210 := derived1210 a h
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c364 := h 363 (by decide)
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1212 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c1206, some c1087, some c1199, some c108, some c1209, some c26, some c1156, some c1211, some c194, some c167, some c22, some c74, some c1164, some c380, some c381, some c185, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1212 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 57) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c192, c1206, c1087, c1199, c108, c1209, c26, c1156, c1211, c194, c167, c22, c74, c1164, c380, c381, c185] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c1206 := derived1206 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1209 := derived1209 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c1156 := derived1156 a h
  have h8 : Entails.eval a c1211 := derived1211 a h
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c1164 := derived1164 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c381 := h 380 (by decide)
  have h16 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1213 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c194, some c1207, some c26, some c167, some c22, some c74, some c1164, some c246, some c381, some c185, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1213 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 57) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c1087, c1199, c108, c194, c1207, c26, c167, c22, c74, c1164, c246, c381, c185] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c1207 := derived1207 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c1164 := derived1164 a h
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1214 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨13, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1214 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c84, some c81, some c380, some c381, some c161, some c369, some c317, some c364, some c151, some c328, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1214 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1214 : lratChecker f1214 p1214 = .success := by decide +kernel
theorem unsat1214 : Unsatisfiable (PosFin 57) f1214 := by
  apply lratCheckerSound f1214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1214
  · intro a ha; simp [p1214] at ha; subst a; trivial
  · exact checked1214
theorem derived1214 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1214 := by
  apply localUnsat_implies_entails f1214 [c74, c84, c81, c380, c381, c161, c369, c317, c364, c151, c328] c1214 unsat1214 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1215 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1215 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c1206, some c1087, some c1199, some c108, some c111, some c1127, some c1212, some c1213, some c6, some c18, some c196, some c1208, some c261, some c26, some c1156, some c1214, some c1139, some c372, some c380, some c1141, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1215 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1215 : lratChecker f1215 p1215 = .success := by decide +kernel
theorem unsat1215 : Unsatisfiable (PosFin 57) f1215 := by
  apply lratCheckerSound f1215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1215
  · intro a ha; simp [p1215] at ha; subst a; trivial
  · exact checked1215
theorem derived1215 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1215 := by
  apply localUnsat_implies_entails f1215 [c192, c1206, c1087, c1199, c108, c111, c1127, c1212, c1213, c6, c18, c196, c1208, c261, c26, c1156, c1214, c1139, c372, c380, c1141] c1215 unsat1215 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c1206 := derived1206 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c1127 := derived1127 a h
  have h7 : Entails.eval a c1212 := derived1212 a h
  have h8 : Entails.eval a c1213 := derived1213 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c1208 := derived1208 a h
  have h13 : Entails.eval a c261 := h 260 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c1156 := derived1156 a h
  have h16 : Entails.eval a c1214 := derived1214 a h
  have h17 : Entails.eval a c1139 := derived1139 a h
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c380 := h 379 (by decide)
  have h20 : Entails.eval a c1141 := derived1141 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1216 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨15, by decide⟩, true), (⟨54, by decide⟩, false), (⟨41, by decide⟩, false), (⟨12, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1216 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c369, some c372, some c1141, some c380, some c471, some c93, some c382, some c377, some c362, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1216 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1216 : lratChecker f1216 p1216 = .success := by decide +kernel
theorem unsat1216 : Unsatisfiable (PosFin 57) f1216 := by
  apply lratCheckerSound f1216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1216
  · intro a ha; simp [p1216] at ha; subst a; trivial
  · exact checked1216
theorem derived1216 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1216 := by
  apply localUnsat_implies_entails f1216 [c108, c369, c372, c1141, c380, c471, c93, c382, c377, c362] c1216 unsat1216 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1141 := derived1141 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c471 := derived471 a h
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1217 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨15, by decide⟩, true), (⟨54, by decide⟩, false), (⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1217 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c21, some c1087, some c1199, some c108, some c29, some c1206, some c1216, some c26, some c262, some c235, some c168, some c594, some c72, some c319, some c156, some c218, some c65, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1217 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1217 : lratChecker f1217 p1217 = .success := by decide +kernel
theorem unsat1217 : Unsatisfiable (PosFin 57) f1217 := by
  apply lratCheckerSound f1217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1217
  · intro a ha; simp [p1217] at ha; subst a; trivial
  · exact checked1217
theorem derived1217 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1217 := by
  apply localUnsat_implies_entails f1217 [c21, c1087, c1199, c108, c29, c1206, c1216, c26, c262, c235, c168, c594, c72, c319, c156, c218, c65] c1217 unsat1217 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1199 := derived1199 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c1206 := derived1206 a h
  have h6 : Entails.eval a c1216 := derived1216 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c594 := derived594 a h
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c156 := h 155 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1218 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1218 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1215, some c257, some c21, some c1087, some c1199, some c108, some c29, some c192, some c1206, some c111, some c6, some c18, some c196, some c1217, some c74, some c380, some c381, some c247, some c185, some c26, some c120, some c369, some c235, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1218 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1218 : lratChecker f1218 p1218 = .success := by decide +kernel
theorem unsat1218 : Unsatisfiable (PosFin 57) f1218 := by
  apply lratCheckerSound f1218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1218
  · intro a ha; simp [p1218] at ha; subst a; trivial
  · exact checked1218
theorem derived1218 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1218 := by
  apply localUnsat_implies_entails f1218 [c1127, c1215, c257, c21, c1087, c1199, c108, c29, c192, c1206, c111, c6, c18, c196, c1217, c74, c380, c381, c247, c185, c26, c120, c369, c235] c1218 unsat1218 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1215 := derived1215 a h
  have h2 : Entails.eval a c257 := h 256 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c1087 := derived1087 a h
  have h5 : Entails.eval a c1199 := derived1199 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c192 := h 191 (by decide)
  have h9 : Entails.eval a c1206 := derived1206 a h
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c1217 := derived1217 a h
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c381 := h 380 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c369 := h 368 (by decide)
  have h23 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1219 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1219 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c1206, some c1087, some c1199, some c108, some c1127, some c1215, some c257, some c29, some c21, some c1218, some c194, some c1207, some c26, some c167, some c369, some c74, some c235, some c248, some c185, some c362, some c379, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1219 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1219 : lratChecker f1219 p1219 = .success := by decide +kernel
theorem unsat1219 : Unsatisfiable (PosFin 57) f1219 := by
  apply lratCheckerSound f1219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1219
  · intro a ha; simp [p1219] at ha; subst a; trivial
  · exact checked1219
theorem derived1219 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1219 := by
  apply localUnsat_implies_entails f1219 [c192, c1206, c1087, c1199, c108, c1127, c1215, c257, c29, c21, c1218, c194, c1207, c26, c167, c369, c74, c235, c248, c185, c362, c379] c1219 unsat1219 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c1206 := derived1206 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c1215 := derived1215 a h
  have h7 : Entails.eval a c257 := h 256 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c1218 := derived1218 a h
  have h11 : Entails.eval a c194 := h 193 (by decide)
  have h12 : Entails.eval a c1207 := derived1207 a h
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c248 := h 247 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c362 := h 361 (by decide)
  have h21 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1220 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1220 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c1006, some c1207, some c257, some c26, some c21, some c167, some c85, some c84, some c368, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1220 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1220 : lratChecker f1220 p1220 = .success := by decide +kernel
theorem unsat1220 : Unsatisfiable (PosFin 57) f1220 := by
  apply lratCheckerSound f1220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1220
  · intro a ha; simp [p1220] at ha; subst a; trivial
  · exact checked1220
theorem derived1220 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1220 := by
  apply localUnsat_implies_entails f1220 [c1087, c1199, c108, c111, c1127, c1006, c1207, c257, c26, c21, c167, c85, c84, c368] c1220 unsat1220 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1006 := derived1006 a h
  have h6 : Entails.eval a c1207 := derived1207 a h
  have h7 : Entails.eval a c257 := h 256 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1221 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1221 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c111, some c1219, some c1220, some c20, some c18, some c196, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1221 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1221 : lratChecker f1221 p1221 = .success := by decide +kernel
theorem unsat1221 : Unsatisfiable (PosFin 57) f1221 := by
  apply lratCheckerSound f1221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1221
  · intro a ha; simp [p1221] at ha; subst a; trivial
  · exact checked1221
theorem derived1221 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1221 := by
  apply localUnsat_implies_entails f1221 [c1087, c1199, c111, c1219, c1220, c20, c18, c196] c1221 unsat1221 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1219 := derived1219 a h
  have h4 : Entails.eval a c1220 := derived1220 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1222 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1222 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c111, some c18, some c1208, some c6, some c108, some c1127, some c20, some c189, some c126, some c1, some c40, some c27, some c242, some c261, some c247, some c262, some c174, some c21, some c74, some c475, some c1133, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1222 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1222 : lratChecker f1222 p1222 = .success := by decide +kernel
theorem unsat1222 : Unsatisfiable (PosFin 57) f1222 := by
  apply lratCheckerSound f1222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1222
  · intro a ha; simp [p1222] at ha; subst a; trivial
  · exact checked1222
theorem derived1222 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1222 := by
  apply localUnsat_implies_entails f1222 [c1087, c1199, c111, c18, c1208, c6, c108, c1127, c20, c189, c126, c1, c40, c27, c242, c261, c247, c262, c174, c21, c74, c475, c1133] c1222 unsat1222 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c1208 := derived1208 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1127 := derived1127 a h
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c247 := h 246 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c174 := h 173 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c74 := h 73 (by decide)
  have h21 : Entails.eval a c475 := derived475 a h
  have h22 : Entails.eval a c1133 := derived1133 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1223 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1223 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c126, some c1, some c1203, some c1123, some c124, some c261, some c65, some c1156, some c151, some c333, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1223 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1223 : lratChecker f1223 p1223 = .success := by decide +kernel
theorem unsat1223 : Unsatisfiable (PosFin 57) f1223 := by
  apply lratCheckerSound f1223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1223
  · intro a ha; simp [p1223] at ha; subst a; trivial
  · exact checked1223
theorem derived1223 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1223 := by
  apply localUnsat_implies_entails f1223 [c189, c126, c1, c1203, c1123, c124, c261, c65, c1156, c151, c333] c1223 unsat1223 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1203 := derived1203 a h
  have h4 : Entails.eval a c1123 := derived1123 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c1156 := derived1156 a h
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1224 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1224 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c662, some c135, some c51, some c56, some c143, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1224 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1224 : lratChecker f1224 p1224 = .success := by decide +kernel
theorem unsat1224 : Unsatisfiable (PosFin 57) f1224 := by
  apply lratCheckerSound f1224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1224
  · intro a ha; simp [p1224] at ha; subst a; trivial
  · exact checked1224
theorem derived1224 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1224 := by
  apply localUnsat_implies_entails f1224 [c662, c135, c51, c56, c143] c1224 unsat1224 (by rfl) a
  have h0 : Entails.eval a c662 := derived662 a h
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1225 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1225 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1221, some c1206, some c1087, some c1199, some c108, some c111, some c1127, some c6, some c18, some c1208, some c1222, some c1223, some c1224, some c120, some c235, some c168, some c74, some c81, some c247, some c369, some c26, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1225 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1225 : lratChecker f1225 p1225 = .success := by decide +kernel
theorem unsat1225 : Unsatisfiable (PosFin 57) f1225 := by
  apply lratCheckerSound f1225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1225
  · intro a ha; simp [p1225] at ha; subst a; trivial
  · exact checked1225
theorem derived1225 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1225 := by
  apply localUnsat_implies_entails f1225 [c1221, c1206, c1087, c1199, c108, c111, c1127, c6, c18, c1208, c1222, c1223, c1224, c120, c235, c168, c74, c81, c247, c369, c26] c1225 unsat1225 (by rfl) a
  have h0 : Entails.eval a c1221 := derived1221 a h
  have h1 : Entails.eval a c1206 := derived1206 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c1127 := derived1127 a h
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c1208 := derived1208 a h
  have h10 : Entails.eval a c1222 := derived1222 a h
  have h11 : Entails.eval a c1223 := derived1223 a h
  have h12 : Entails.eval a c1224 := derived1224 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c369 := h 368 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1226 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1226 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1206, some c1087, some c1199, some c108, some c1225, some c194, some c193, some c1207, some c26, some c167, some c22, some c74, some c81, some c369, some c235, some c248, some c362, some c185, some c379, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1226 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1226 : lratChecker f1226 p1226 = .success := by decide +kernel
theorem unsat1226 : Unsatisfiable (PosFin 57) f1226 := by
  apply lratCheckerSound f1226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1226
  · intro a ha; simp [p1226] at ha; subst a; trivial
  · exact checked1226
theorem derived1226 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1226 := by
  apply localUnsat_implies_entails f1226 [c1206, c1087, c1199, c108, c1225, c194, c193, c1207, c26, c167, c22, c74, c81, c369, c235, c248, c362, c185, c379] c1226 unsat1226 (by rfl) a
  have h0 : Entails.eval a c1206 := derived1206 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1199 := derived1199 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1225 := derived1225 a h
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c1207 := derived1207 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c248 := h 247 (by decide)
  have h16 : Entails.eval a c362 := h 361 (by decide)
  have h17 : Entails.eval a c185 := h 184 (by decide)
  have h18 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1227 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1227 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c206, some c310, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1227 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1227 : lratChecker f1227 p1227 = .success := by decide +kernel
theorem unsat1227 : Unsatisfiable (PosFin 57) f1227 := by
  apply lratCheckerSound f1227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1227
  · intro a ha; simp [p1227] at ha; subst a; trivial
  · exact checked1227
theorem derived1227 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1227 := by
  apply localUnsat_implies_entails f1227 [c210, c206, c310] c1227 unsat1227 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1228 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨43, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1228 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c111, some c1127, some c185, some c380, some c379, some c246, some c1164, some c102, some c183, some c257, some c170, some c981, some c1227, some c49, some c286, some c200, some c133, some c343, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1228 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1228 : lratChecker f1228 p1228 = .success := by decide +kernel
theorem unsat1228 : Unsatisfiable (PosFin 57) f1228 := by
  apply lratCheckerSound f1228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1228
  · intro a ha; simp [p1228] at ha; subst a; trivial
  · exact checked1228
theorem derived1228 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1228 := by
  apply localUnsat_implies_entails f1228 [c1087, c1199, c111, c1127, c185, c380, c379, c246, c1164, c102, c183, c257, c170, c981, c1227, c49, c286, c200, c133, c343] c1228 unsat1228 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1127 := derived1127 a h
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c1164 := derived1164 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c981 := derived981 a h
  have h14 : Entails.eval a c1227 := derived1227 a h
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c133 := h 132 (by decide)
  have h19 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1229 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1229 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1206, some c1087, some c1199, some c108, some c111, some c1127, some c194, some c193, some c1207, some c1220, some c26, some c167, some c861, some c22, some c74, some c84, some c81, some c375, some c374, some c369, some c1228, some c377, some c248, some c378, some c102, some c237, some c363, some c252, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1229 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1229 : lratChecker f1229 p1229 = .success := by decide +kernel
theorem unsat1229 : Unsatisfiable (PosFin 57) f1229 := by
  apply lratCheckerSound f1229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1229
  · intro a ha; simp [p1229] at ha; subst a; trivial
  · exact checked1229
theorem derived1229 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1229 := by
  apply localUnsat_implies_entails f1229 [c1206, c1087, c1199, c108, c111, c1127, c194, c193, c1207, c1220, c26, c167, c861, c22, c74, c84, c81, c375, c374, c369, c1228, c377, c248, c378, c102, c237, c363, c252] c1229 unsat1229 (by rfl) a
  have h0 : Entails.eval a c1206 := derived1206 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1199 := derived1199 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c1207 := derived1207 a h
  have h9 : Entails.eval a c1220 := derived1220 a h
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c167 := h 166 (by decide)
  have h12 : Entails.eval a c861 := derived861 a h
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c81 := h 80 (by decide)
  have h17 : Entails.eval a c375 := h 374 (by decide)
  have h18 : Entails.eval a c374 := h 373 (by decide)
  have h19 : Entails.eval a c369 := h 368 (by decide)
  have h20 : Entails.eval a c1228 := derived1228 a h
  have h21 : Entails.eval a c377 := h 376 (by decide)
  have h22 : Entails.eval a c248 := h 247 (by decide)
  have h23 : Entails.eval a c378 := h 377 (by decide)
  have h24 : Entails.eval a c102 := h 101 (by decide)
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c363 := h 362 (by decide)
  have h27 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1230 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨16, by decide⟩, true), (⟨54, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1230 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c380, some c471, some c74, some c93, some c382, some c165, some c377, some c183, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1230 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1230 : lratChecker f1230 p1230 = .success := by decide +kernel
theorem unsat1230 : Unsatisfiable (PosFin 57) f1230 := by
  apply lratCheckerSound f1230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1230
  · intro a ha; simp [p1230] at ha; subst a; trivial
  · exact checked1230
theorem derived1230 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1230 := by
  apply localUnsat_implies_entails f1230 [c108, c380, c471, c74, c93, c382, c165, c377, c183] c1230 unsat1230 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c471 := derived471 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c165 := h 164 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1231 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1231 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c381, some c93, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1231 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1231 : lratChecker f1231 p1231 = .success := by decide +kernel
theorem unsat1231 : Unsatisfiable (PosFin 57) f1231 := by
  apply lratCheckerSound f1231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1231
  · intro a ha; simp [p1231] at ha; subst a; trivial
  · exact checked1231
theorem derived1231 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1231 := by
  apply localUnsat_implies_entails f1231 [c377, c381, c93] c1231 unsat1231 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1232 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨43, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1232 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1231, some c1230, some c185, some c192, some c1224, some c1223, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1232 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1232 : lratChecker f1232 p1232 = .success := by decide +kernel
theorem unsat1232 : Unsatisfiable (PosFin 57) f1232 := by
  apply lratCheckerSound f1232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1232
  · intro a ha; simp [p1232] at ha; subst a; trivial
  · exact checked1232
theorem derived1232 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1232 := by
  apply localUnsat_implies_entails f1232 [c108, c1231, c1230, c185, c192, c1224, c1223] c1232 unsat1232 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c1230 := derived1230 a h
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c1224 := derived1224 a h
  have h6 : Entails.eval a c1223 := derived1223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1233 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1233 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c168, some c371, some c364, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1233 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1233 : lratChecker f1233 p1233 = .success := by decide +kernel
theorem unsat1233 : Unsatisfiable (PosFin 57) f1233 := by
  apply lratCheckerSound f1233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1233
  · intro a ha; simp [p1233] at ha; subst a; trivial
  · exact checked1233
theorem derived1233 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1233 := by
  apply localUnsat_implies_entails f1233 [c168, c371, c364] c1233 unsat1233 (by rfl) a
  have h0 : Entails.eval a c168 := h 167 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1234 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1234 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c1229, some c6, some c1231, some c111, some c18, some c1208, some c1233, some c74, some c84, some c247, some c374, some c26, some c364, some c369, some c81, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1234 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1234 : lratChecker f1234 p1234 = .success := by decide +kernel
theorem unsat1234 : Unsatisfiable (PosFin 57) f1234 := by
  apply lratCheckerSound f1234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1234
  · intro a ha; simp [p1234] at ha; subst a; trivial
  · exact checked1234
theorem derived1234 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1234 := by
  apply localUnsat_implies_entails f1234 [c1087, c1199, c108, c1229, c6, c1231, c111, c18, c1208, c1233, c74, c84, c247, c374, c26, c364, c369, c81] c1234 unsat1234 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1229 := derived1229 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c1208 := derived1208 a h
  have h9 : Entails.eval a c1233 := derived1233 a h
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c364 := h 363 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1235 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1235 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c1206, some c1226, some c1229, some c6, some c18, some c1222, some c1208, some c1232, some c120, some c1234, some c380, some c471, some c74, some c252, some c168, some c371, some c237, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1235 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1235 : lratChecker f1235 p1235 = .success := by decide +kernel
theorem unsat1235 : Unsatisfiable (PosFin 57) f1235 := by
  apply lratCheckerSound f1235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1235
  · intro a ha; simp [p1235] at ha; subst a; trivial
  · exact checked1235
theorem derived1235 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1235 := by
  apply localUnsat_implies_entails f1235 [c1087, c1199, c108, c111, c1127, c1206, c1226, c1229, c6, c18, c1222, c1208, c1232, c120, c1234, c380, c471, c74, c252, c168, c371, c237] c1235 unsat1235 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1206 := derived1206 a h
  have h6 : Entails.eval a c1226 := derived1226 a h
  have h7 : Entails.eval a c1229 := derived1229 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c1222 := derived1222 a h
  have h11 : Entails.eval a c1208 := derived1208 a h
  have h12 : Entails.eval a c1232 := derived1232 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c1234 := derived1234 a h
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c471 := derived471 a h
  have h17 : Entails.eval a c74 := h 73 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  have h19 : Entails.eval a c168 := h 167 (by decide)
  have h20 : Entails.eval a c371 := h 370 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1236 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1236 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c6, some c18, some c20, some c126, some c33, some c40, some c27, some c261, some c247, some c262, some c174, some c74, some c1133, some c90, some c237, some c373, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1236 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1236 : lratChecker f1236 p1236 = .success := by decide +kernel
theorem unsat1236 : Unsatisfiable (PosFin 57) f1236 := by
  apply lratCheckerSound f1236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1236
  · intro a ha; simp [p1236] at ha; subst a; trivial
  · exact checked1236
theorem derived1236 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1236 := by
  apply localUnsat_implies_entails f1236 [c1087, c1199, c108, c111, c1127, c6, c18, c20, c126, c33, c40, c27, c261, c247, c262, c174, c74, c1133, c90, c237, c373] c1236 unsat1236 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c247 := h 246 (by decide)
  have h14 : Entails.eval a c262 := h 261 (by decide)
  have h15 : Entails.eval a c174 := h 173 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c1133 := derived1133 a h
  have h18 : Entails.eval a c90 := h 89 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1237 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1237 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c381, some c185, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1237 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1237 : lratChecker f1237 p1237 = .success := by decide +kernel
theorem unsat1237 : Unsatisfiable (PosFin 57) f1237 := by
  apply lratCheckerSound f1237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1237
  · intro a ha; simp [p1237] at ha; subst a; trivial
  · exact checked1237
theorem derived1237 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1237 := by
  apply localUnsat_implies_entails f1237 [c380, c381, c185] c1237 unsat1237 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1238 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1238 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c97, some c471, some c254, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1238 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1238 : lratChecker f1238 p1238 = .success := by decide +kernel
theorem unsat1238 : Unsatisfiable (PosFin 57) f1238 := by
  apply lratCheckerSound f1238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1238
  · intro a ha; simp [p1238] at ha; subst a; trivial
  · exact checked1238
theorem derived1238 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1238 := by
  apply localUnsat_implies_entails f1238 [c108, c97, c471, c254] c1238 unsat1238 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c471 := derived471 a h
  have h3 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1239 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1239 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c111, some c1127, some c1236, some c194, some c193, some c1006, some c1238, some c1237, some c104, some c102, some c254, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1239 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1239 : lratChecker f1239 p1239 = .success := by decide +kernel
theorem unsat1239 : Unsatisfiable (PosFin 57) f1239 := by
  apply lratCheckerSound f1239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1239
  · intro a ha; simp [p1239] at ha; subst a; trivial
  · exact checked1239
theorem derived1239 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1239 := by
  apply localUnsat_implies_entails f1239 [c1087, c1199, c108, c111, c1127, c1236, c194, c193, c1006, c1238, c1237, c104, c102, c254] c1239 unsat1239 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1236 := derived1236 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c1006 := derived1006 a h
  have h9 : Entails.eval a c1238 := derived1238 a h
  have h10 : Entails.eval a c1237 := derived1237 a h
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1240 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1240 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c111, some c107, some c19, some c126, some c1052, some c49, some c51, some c144, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1240 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1240 : lratChecker f1240 p1240 = .success := by decide +kernel
theorem unsat1240 : Unsatisfiable (PosFin 57) f1240 := by
  apply lratCheckerSound f1240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1240
  · intro a ha; simp [p1240] at ha; subst a; trivial
  · exact checked1240
theorem derived1240 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1240 := by
  apply localUnsat_implies_entails f1240 [c257, c111, c107, c19, c126, c1052, c49, c51, c144] c1240 unsat1240 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c1052 := derived1052 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1241 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1241 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c193, some c194, some c1239, some c1087, some c1199, some c108, some c1127, some c78, some c167, some c22, some c74, some c119, some c1164, some c1204, some c1240, some c1235, some c1229, some c81, some c8, some c369, some c248, some c235, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1241 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1241 : lratChecker f1241 p1241 = .success := by decide +kernel
theorem unsat1241 : Unsatisfiable (PosFin 57) f1241 := by
  apply lratCheckerSound f1241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1241
  · intro a ha; simp [p1241] at ha; subst a; trivial
  · exact checked1241
theorem derived1241 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1241 := by
  apply localUnsat_implies_entails f1241 [c193, c194, c1239, c1087, c1199, c108, c1127, c78, c167, c22, c74, c119, c1164, c1204, c1240, c1235, c1229, c81, c8, c369, c248, c235] c1241 unsat1241 (by rfl) a
  have h0 : Entails.eval a c193 := h 192 (by decide)
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c1239 := derived1239 a h
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c1199 := derived1199 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1127 := derived1127 a h
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c1164 := derived1164 a h
  have h13 : Entails.eval a c1204 := derived1204 a h
  have h14 : Entails.eval a c1240 := derived1240 a h
  have h15 : Entails.eval a c1235 := derived1235 a h
  have h16 : Entails.eval a c1229 := derived1229 a h
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c369 := h 368 (by decide)
  have h20 : Entails.eval a c248 := h 247 (by decide)
  have h21 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1242 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1242 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c1240, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1242 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1242 : lratChecker f1242 p1242 = .success := by decide +kernel
theorem unsat1242 : Unsatisfiable (PosFin 57) f1242 := by
  apply lratCheckerSound f1242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1242
  · intro a ha; simp [p1242] at ha; subst a; trivial
  · exact checked1242
theorem derived1242 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1242 := by
  apply localUnsat_implies_entails f1242 [c264, c1240] c1242 unsat1242 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c1240 := derived1240 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1243 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨48, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨42, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1243 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c594, some c323, some c198, some c284, some c145, some c211, some c49, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1243 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1243 : lratChecker f1243 p1243 = .success := by decide +kernel
theorem unsat1243 : Unsatisfiable (PosFin 57) f1243 := by
  apply lratCheckerSound f1243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1243
  · intro a ha; simp [p1243] at ha; subst a; trivial
  · exact checked1243
theorem derived1243 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1243 := by
  apply localUnsat_implies_entails f1243 [c594, c323, c198, c284, c145, c211, c49] c1243 unsat1243 (by rfl) a
  have h0 : Entails.eval a c594 := derived594 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1244 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1244 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1239, some c1087, some c1199, some c108, some c111, some c1127, some c194, some c193, some c1241, some c1237, some c74, some c167, some c26, some c1207, some c119, some c107, some c8, some c19, some c255, some c28, some c1242, some c1243, some c263, some c122, some c1203, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1244 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1244 : lratChecker f1244 p1244 = .success := by decide +kernel
theorem unsat1244 : Unsatisfiable (PosFin 57) f1244 := by
  apply lratCheckerSound f1244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1244
  · intro a ha; simp [p1244] at ha; subst a; trivial
  · exact checked1244
theorem derived1244 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1244 := by
  apply localUnsat_implies_entails f1244 [c1239, c1087, c1199, c108, c111, c1127, c194, c193, c1241, c1237, c74, c167, c26, c1207, c119, c107, c8, c19, c255, c28, c1242, c1243, c263, c122, c1203] c1244 unsat1244 (by rfl) a
  have h0 : Entails.eval a c1239 := derived1239 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1199 := derived1199 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c1241 := derived1241 a h
  have h9 : Entails.eval a c1237 := derived1237 a h
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c167 := h 166 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c1207 := derived1207 a h
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c107 := h 106 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c255 := h 254 (by decide)
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c1242 := derived1242 a h
  have h21 : Entails.eval a c1243 := derived1243 a h
  have h22 : Entails.eval a c263 := h 262 (by decide)
  have h23 : Entails.eval a c122 := h 121 (by decide)
  have h24 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1245 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1245 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c263, some c122, some c1203, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1245 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1245 : lratChecker f1245 p1245 = .success := by decide +kernel
theorem unsat1245 : Unsatisfiable (PosFin 57) f1245 := by
  apply lratCheckerSound f1245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1245
  · intro a ha; simp [p1245] at ha; subst a; trivial
  · exact checked1245
theorem derived1245 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1245 := by
  apply localUnsat_implies_entails f1245 [c264, c263, c122, c1203] c1245 unsat1245 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1246 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨15, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1246 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c255, some c184, some c594, some c665, some c346, some c67, some c134, some c199, some c305, some c51, some c212, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1246 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1246 : lratChecker f1246 p1246 = .success := by decide +kernel
theorem unsat1246 : Unsatisfiable (PosFin 57) f1246 := by
  apply lratCheckerSound f1246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1246
  · intro a ha; simp [p1246] at ha; subst a; trivial
  · exact checked1246
theorem derived1246 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1246 := by
  apply localUnsat_implies_entails f1246 [c589, c255, c184, c594, c665, c346, c67, c134, c199, c305, c51, c212] c1246 unsat1246 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c346 := h 345 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1247 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1247 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1239, some c1235, some c107, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1247 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1247 : lratChecker f1247 p1247 = .success := by decide +kernel
theorem unsat1247 : Unsatisfiable (PosFin 57) f1247 := by
  apply lratCheckerSound f1247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1247
  · intro a ha; simp [p1247] at ha; subst a; trivial
  · exact checked1247
theorem derived1247 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1247 := by
  apply localUnsat_implies_entails f1247 [c1239, c1235, c107] c1247 unsat1247 (by rfl) a
  have h0 : Entails.eval a c1239 := derived1239 a h
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1248 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1248 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c1203, some c192, some c196, some c1246, some c184, some c1156, some c344, some c346, some c157, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1248 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1248 : lratChecker f1248 p1248 = .success := by decide +kernel
theorem unsat1248 : Unsatisfiable (PosFin 57) f1248 := by
  apply lratCheckerSound f1248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1248
  · intro a ha; simp [p1248] at ha; subst a; trivial
  · exact checked1248
theorem derived1248 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1248 := by
  apply localUnsat_implies_entails f1248 [c589, c1203, c192, c196, c1246, c184, c1156, c344, c346, c157] c1248 unsat1248 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c1203 := derived1203 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c1246 := derived1246 a h
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c1156 := derived1156 a h
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1249 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1249 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c252, some c184, some c179, some c189, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1249 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1249 : lratChecker f1249 p1249 = .success := by decide +kernel
theorem unsat1249 : Unsatisfiable (PosFin 57) f1249 := by
  apply lratCheckerSound f1249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1249
  · intro a ha; simp [p1249] at ha; subst a; trivial
  · exact checked1249
theorem derived1249 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1249 := by
  apply localUnsat_implies_entails f1249 [c124, c252, c184, c179, c189] c1249 unsat1249 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1250 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1250 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1247, some c1087, some c1127, some c1199, some c1239, some c111, some c1244, some c18, some c1245, some c6, some c108, some c8, some c377, some c589, some c381, some c1231, some c471, some c1249, some c1248, some c126, some c1242, some c1150, some c192, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1250 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1250 : lratChecker f1250 p1250 = .success := by decide +kernel
theorem unsat1250 : Unsatisfiable (PosFin 57) f1250 := by
  apply lratCheckerSound f1250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1250
  · intro a ha; simp [p1250] at ha; subst a; trivial
  · exact checked1250
theorem derived1250 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1250 := by
  apply localUnsat_implies_entails f1250 [c1247, c1087, c1127, c1199, c1239, c111, c1244, c18, c1245, c6, c108, c8, c377, c589, c381, c1231, c471, c1249, c1248, c126, c1242, c1150, c192] c1250 unsat1250 (by rfl) a
  have h0 : Entails.eval a c1247 := derived1247 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c1239 := derived1239 a h
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c1244 := derived1244 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c1245 := derived1245 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c589 := derived589 a h
  have h14 : Entails.eval a c381 := h 380 (by decide)
  have h15 : Entails.eval a c1231 := derived1231 a h
  have h16 : Entails.eval a c471 := derived471 a h
  have h17 : Entails.eval a c1249 := derived1249 a h
  have h18 : Entails.eval a c1248 := derived1248 a h
  have h19 : Entails.eval a c126 := h 125 (by decide)
  have h20 : Entails.eval a c1242 := derived1242 a h
  have h21 : Entails.eval a c1150 := derived1150 a h
  have h22 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1251 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨56, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1251 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1199, some c108, some c1244, some c6, some c1231, some c381, some c377, some c1127, some c1239, some c111, some c18, some c1245, some c257, some c126, some c1052, some c1150, some c49, some c51, some c192, some c144, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1251 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1251 : lratChecker f1251 p1251 = .success := by decide +kernel
theorem unsat1251 : Unsatisfiable (PosFin 57) f1251 := by
  apply lratCheckerSound f1251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1251
  · intro a ha; simp [p1251] at ha; subst a; trivial
  · exact checked1251
theorem derived1251 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1251 := by
  apply localUnsat_implies_entails f1251 [c1087, c1199, c108, c1244, c6, c1231, c381, c377, c1127, c1239, c111, c18, c1245, c257, c126, c1052, c1150, c49, c51, c192, c144] c1251 unsat1251 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1199 := derived1199 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1244 := derived1244 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c1127 := derived1127 a h
  have h9 : Entails.eval a c1239 := derived1239 a h
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c1245 := derived1245 a h
  have h13 : Entails.eval a c257 := h 256 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c1052 := derived1052 a h
  have h16 : Entails.eval a c1150 := derived1150 a h
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1252 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1252 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1250, some c1247, some c1087, some c1199, some c111, some c1244, some c18, some c6, some c1239, some c108, some c1127, some c377, some c589, some c381, some c1231, some c471, some c74, some c1249, some c168, some c28, some c255, some c120, some c1251, some c1203, some c518, some c192, some c196, some c1053, some c209, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1252 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1252 : lratChecker f1252 p1252 = .success := by decide +kernel
theorem unsat1252 : Unsatisfiable (PosFin 57) f1252 := by
  apply lratCheckerSound f1252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1252
  · intro a ha; simp [p1252] at ha; subst a; trivial
  · exact checked1252
theorem derived1252 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1252 := by
  apply localUnsat_implies_entails f1252 [c1250, c1247, c1087, c1199, c111, c1244, c18, c6, c1239, c108, c1127, c377, c589, c381, c1231, c471, c74, c1249, c168, c28, c255, c120, c1251, c1203, c518, c192, c196, c1053, c209] c1252 unsat1252 (by rfl) a
  have h0 : Entails.eval a c1250 := derived1250 a h
  have h1 : Entails.eval a c1247 := derived1247 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1244 := derived1244 a h
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c1239 := derived1239 a h
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c1127 := derived1127 a h
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c589 := derived589 a h
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c1231 := derived1231 a h
  have h15 : Entails.eval a c471 := derived471 a h
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c1249 := derived1249 a h
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c255 := h 254 (by decide)
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c1251 := derived1251 a h
  have h23 : Entails.eval a c1203 := derived1203 a h
  have h24 : Entails.eval a c518 := derived518 a h
  have h25 : Entails.eval a c192 := h 191 (by decide)
  have h26 : Entails.eval a c196 := h 195 (by decide)
  have h27 : Entails.eval a c1053 := derived1053 a h
  have h28 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1253 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨46, by decide⟩, false), (⟨24, by decide⟩, true), (⟨22, by decide⟩, true), (⟨48, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1253 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1156, some c330, some c223, some c204, some c67, some c291, some c203, some c210, some c51, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1253 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1253 : lratChecker f1253 p1253 = .success := by decide +kernel
theorem unsat1253 : Unsatisfiable (PosFin 57) f1253 := by
  apply lratCheckerSound f1253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1253
  · intro a ha; simp [p1253] at ha; subst a; trivial
  · exact checked1253
theorem derived1253 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1253 := by
  apply localUnsat_implies_entails f1253 [c1156, c330, c223, c204, c67, c291, c203, c210, c51] c1253 unsat1253 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c330 := h 329 (by decide)
  have h2 : Entails.eval a c223 := h 222 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1254 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1254 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1127, some c1199, some c111, some c108, some c1239, some c1244, some c6, some c18, some c1245, some c1247, some c1250, some c1252, some c103, some c80, some c168, some c22, some c74, some c247, some c120, some c380, some c26, some c369, some c81, some c1253, some c254, some c126, some c1152, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1254 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1254 : lratChecker f1254 p1254 = .success := by decide +kernel
theorem unsat1254 : Unsatisfiable (PosFin 57) f1254 := by
  apply lratCheckerSound f1254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1254
  · intro a ha; simp [p1254] at ha; subst a; trivial
  · exact checked1254
theorem derived1254 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1254 := by
  apply localUnsat_implies_entails f1254 [c1087, c1127, c1199, c111, c108, c1239, c1244, c6, c18, c1245, c1247, c1250, c1252, c103, c80, c168, c22, c74, c247, c120, c380, c26, c369, c81, c1253, c254, c126, c1152] c1254 unsat1254 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1127 := derived1127 a h
  have h2 : Entails.eval a c1199 := derived1199 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1239 := derived1239 a h
  have h6 : Entails.eval a c1244 := derived1244 a h
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c1245 := derived1245 a h
  have h10 : Entails.eval a c1247 := derived1247 a h
  have h11 : Entails.eval a c1250 := derived1250 a h
  have h12 : Entails.eval a c1252 := derived1252 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c22 := h 21 (by decide)
  have h17 : Entails.eval a c74 := h 73 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c120 := h 119 (by decide)
  have h20 : Entails.eval a c380 := h 379 (by decide)
  have h21 : Entails.eval a c26 := h 25 (by decide)
  have h22 : Entails.eval a c369 := h 368 (by decide)
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c1253 := derived1253 a h
  have h25 : Entails.eval a c254 := h 253 (by decide)
  have h26 : Entails.eval a c126 := h 125 (by decide)
  have h27 : Entails.eval a c1152 := derived1152 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1255 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, false), (⟨48, by decide⟩, false), (⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1255 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c369, some c84, some c231, some c172, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1255 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1255 : lratChecker f1255 p1255 = .success := by decide +kernel
theorem unsat1255 : Unsatisfiable (PosFin 57) f1255 := by
  apply lratCheckerSound f1255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1255
  · intro a ha; simp [p1255] at ha; subst a; trivial
  · exact checked1255
theorem derived1255 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1255 := by
  apply localUnsat_implies_entails f1255 [c373, c369, c84, c231, c172] c1255 unsat1255 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1256 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1256 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c12, some c126, some c257, some c103, some c80, some c254, some c184, some c124, some c1255, some c90, some c172, some c643, some c363, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1256 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1256 : lratChecker f1256 p1256 = .success := by decide +kernel
theorem unsat1256 : Unsatisfiable (PosFin 57) f1256 := by
  apply lratCheckerSound f1256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1256
  · intro a ha; simp [p1256] at ha; subst a; trivial
  · exact checked1256
theorem derived1256 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1256 := by
  apply localUnsat_implies_entails f1256 [c1254, c12, c126, c257, c103, c80, c254, c184, c124, c1255, c90, c172, c643, c363] c1256 unsat1256 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c254 := h 253 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c1255 := derived1255 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c643 := derived643 a h
  have h13 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1257 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨56, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1257 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c1254, some c111, some c108, some c12, some c1256, some c107, some c9, some c21, some c161, some c84, some c1133, some c90, some c364, some c373, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1257 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1257 : lratChecker f1257 p1257 = .success := by decide +kernel
theorem unsat1257 : Unsatisfiable (PosFin 57) f1257 := by
  apply lratCheckerSound f1257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1257
  · intro a ha; simp [p1257] at ha; subst a; trivial
  · exact checked1257
theorem derived1257 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1257 := by
  apply localUnsat_implies_entails f1257 [c257, c1254, c111, c108, c12, c1256, c107, c9, c21, c161, c84, c1133, c90, c364, c373] c1257 unsat1257 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c1256 := derived1256 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c1133 := derived1133 a h
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c364 := h 363 (by decide)
  have h14 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1258 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1258 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c21, some c162, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p1258 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1258 : lratChecker f1258 p1258 = .success := by decide +kernel
theorem unsat1258 : Unsatisfiable (PosFin 57) f1258 := by
  apply lratCheckerSound f1258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1258
  · intro a ha; simp [p1258] at ha; subst a; trivial
  · exact checked1258
theorem derived1258 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1258 := by
  apply localUnsat_implies_entails f1258 [c9, c21, c162] c1258 unsat1258 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1259 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨56, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1259 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c108, some c2, some c257, some c1257, some c380, some c6, some c78, some c1258, some c107, some c8, some c80, some c726, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1259 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1259 : lratChecker f1259 p1259 = .success := by decide +kernel
theorem unsat1259 : Unsatisfiable (PosFin 57) f1259 := by
  apply lratCheckerSound f1259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1259
  · intro a ha; simp [p1259] at ha; subst a; trivial
  · exact checked1259
theorem derived1259 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1259 := by
  apply localUnsat_implies_entails f1259 [c1254, c108, c2, c257, c1257, c380, c6, c78, c1258, c107, c8, c80, c726] c1259 unsat1259 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c1257 := derived1257 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c1258 := derived1258 a h
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1260 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1260 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c17, some c191, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1260 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1260 : lratChecker f1260 p1260 = .success := by decide +kernel
theorem unsat1260 : Unsatisfiable (PosFin 57) f1260 := by
  apply lratCheckerSound f1260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1260
  · intro a ha; simp [p1260] at ha; subst a; trivial
  · exact checked1260
theorem derived1260 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1260 := by
  apply localUnsat_implies_entails f1260 [c16, c17, c191] c1260 unsat1260 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1261 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1261 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c112, some c106, some c1260, some c192, some c193, some c189, some c191, some c957, some c965, some c742, some c58, some c63, some c42, some c313, some c265, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1261 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1261 : lratChecker f1261 p1261 = .success := by decide +kernel
theorem unsat1261 : Unsatisfiable (PosFin 57) f1261 := by
  apply lratCheckerSound f1261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1261
  · intro a ha; simp [p1261] at ha; subst a; trivial
  · exact checked1261
theorem derived1261 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1261 := by
  apply localUnsat_implies_entails f1261 [c108, c112, c106, c1260, c192, c193, c189, c191, c957, c965, c742, c58, c63, c42, c313, c265] c1261 unsat1261 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1260 := derived1260 a h
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c957 := derived957 a h
  have h9 : Entails.eval a c965 := derived965 a h
  have h10 : Entails.eval a c742 := derived742 a h
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c313 := h 312 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1262 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1262 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c342, some c155, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1262 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1262 : lratChecker f1262 p1262 = .success := by decide +kernel
theorem unsat1262 : Unsatisfiable (PosFin 57) f1262 := by
  apply lratCheckerSound f1262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1262
  · intro a ha; simp [p1262] at ha; subst a; trivial
  · exact checked1262
theorem derived1262 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1262 := by
  apply localUnsat_implies_entails f1262 [c347, c342, c155] c1262 unsat1262 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1263 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1263 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c589, some c182, some c1262, some c135, some c308, some c303, some c143, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1263 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1263 : lratChecker f1263 p1263 = .success := by decide +kernel
theorem unsat1263 : Unsatisfiable (PosFin 57) f1263 := by
  apply lratCheckerSound f1263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1263
  · intro a ha; simp [p1263] at ha; subst a; trivial
  · exact checked1263
theorem derived1263 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1263 := by
  apply localUnsat_implies_entails f1263 [c8, c589, c182, c1262, c135, c308, c303, c143] c1263 unsat1263 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c1262 := derived1262 a h
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1264 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1264 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c63, some c265, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1264 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1264 : lratChecker f1264 p1264 = .success := by decide +kernel
theorem unsat1264 : Unsatisfiable (PosFin 57) f1264 := by
  apply lratCheckerSound f1264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1264
  · intro a ha; simp [p1264] at ha; subst a; trivial
  · exact checked1264
theorem derived1264 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1264 := by
  apply localUnsat_implies_entails f1264 [c58, c63, c265] c1264 unsat1264 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1265 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1265 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c118, some c522, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1265 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1265 : lratChecker f1265 p1265 = .success := by decide +kernel
theorem unsat1265 : Unsatisfiable (PosFin 57) f1265 := by
  apply lratCheckerSound f1265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1265
  · intro a ha; simp [p1265] at ha; subst a; trivial
  · exact checked1265
theorem derived1265 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1265 := by
  apply localUnsat_implies_entails f1265 [c120, c118, c522] c1265 unsat1265 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1266 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1266 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c131, some c63, some c45, some c198, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1266 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1266 : lratChecker f1266 p1266 = .success := by decide +kernel
theorem unsat1266 : Unsatisfiable (PosFin 57) f1266 := by
  apply lratCheckerSound f1266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1266
  · intro a ha; simp [p1266] at ha; subst a; trivial
  · exact checked1266
theorem derived1266 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1266 := by
  apply localUnsat_implies_entails f1266 [c154, c131, c63, c45, c198] c1266 unsat1266 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1267 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1267 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1266, some c61, some c198, some c47, some c45, some c142, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1267 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1267 : lratChecker f1267 p1267 = .success := by decide +kernel
theorem unsat1267 : Unsatisfiable (PosFin 57) f1267 := by
  apply lratCheckerSound f1267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1267
  · intro a ha; simp [p1267] at ha; subst a; trivial
  · exact checked1267
theorem derived1267 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1267 := by
  apply localUnsat_implies_entails f1267 [c1266, c61, c198, c47, c45, c142] c1267 unsat1267 (by rfl) a
  have h0 : Entails.eval a c1266 := derived1266 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1268 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1268 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c112, some c106, some c1260, some c193, some c192, some c1261, some c7, some c1263, some c1265, some c1267, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1268 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1268 : lratChecker f1268 p1268 = .success := by decide +kernel
theorem unsat1268 : Unsatisfiable (PosFin 57) f1268 := by
  apply lratCheckerSound f1268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1268
  · intro a ha; simp [p1268] at ha; subst a; trivial
  · exact checked1268
theorem derived1268 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1268 := by
  apply localUnsat_implies_entails f1268 [c108, c112, c106, c1260, c193, c192, c1261, c7, c1263, c1265, c1267] c1268 unsat1268 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1260 := derived1260 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c1261 := derived1261 a h
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c1263 := derived1263 a h
  have h9 : Entails.eval a c1265 := derived1265 a h
  have h10 : Entails.eval a c1267 := derived1267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1269 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1269 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c131, some c63, some c45, some c130, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1269 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1269 : lratChecker f1269 p1269 = .success := by decide +kernel
theorem unsat1269 : Unsatisfiable (PosFin 57) f1269 := by
  apply lratCheckerSound f1269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1269
  · intro a ha; simp [p1269] at ha; subst a; trivial
  · exact checked1269
theorem derived1269 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1269 := by
  apply localUnsat_implies_entails f1269 [c154, c131, c63, c45, c130] c1269 unsat1269 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1270 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1270 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1269, some c61, some c130, some c47, some c45, some c142, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1270 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1270 : lratChecker f1270 p1270 = .success := by decide +kernel
theorem unsat1270 : Unsatisfiable (PosFin 57) f1270 := by
  apply lratCheckerSound f1270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1270
  · intro a ha; simp [p1270] at ha; subst a; trivial
  · exact checked1270
theorem derived1270 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1270 := by
  apply localUnsat_implies_entails f1270 [c1269, c61, c130, c47, c45, c142] c1270 unsat1270 (by rfl) a
  have h0 : Entails.eval a c1269 := derived1269 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1271 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1271 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c671, some c522, some c256, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1271 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1271 : lratChecker f1271 p1271 = .success := by decide +kernel
theorem unsat1271 : Unsatisfiable (PosFin 57) f1271 := by
  apply lratCheckerSound f1271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1271
  · intro a ha; simp [p1271] at ha; subst a; trivial
  · exact checked1271
theorem derived1271 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1271 := by
  apply localUnsat_implies_entails f1271 [c124, c671, c522, c256] c1271 unsat1271 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1272 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1272 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c7, some c822, some c131, some c155, some c50, some c45, some c347, some c130, some c141, some c63, some c308, some c303, some c1271, some c208, some c215, some c262, some c256, some c228, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1272 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1272 : lratChecker f1272 p1272 = .success := by decide +kernel
theorem unsat1272 : Unsatisfiable (PosFin 57) f1272 := by
  apply lratCheckerSound f1272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1272
  · intro a ha; simp [p1272] at ha; subst a; trivial
  · exact checked1272
theorem derived1272 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1272 := by
  apply localUnsat_implies_entails f1272 [c112, c7, c822, c131, c155, c50, c45, c347, c130, c141, c63, c308, c303, c1271, c208, c215, c262, c256, c228] c1272 unsat1272 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c822 := derived822 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c347 := h 346 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c303 := h 302 (by decide)
  have h13 : Entails.eval a c1271 := derived1271 a h
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c215 := h 214 (by decide)
  have h16 : Entails.eval a c262 := h 261 (by decide)
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1273 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1273 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c112, some c1260, some c822, some c189, some c7, some c1270, some c190, some c8, some c1272, some c66, some c61, some c130, some c153, some c47, some c45, some c342, some c347, some c143, some c1271, some c308, some c220, some c227, some c262, some c256, some c216, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1273 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1273 : lratChecker f1273 p1273 = .success := by decide +kernel
theorem unsat1273 : Unsatisfiable (PosFin 57) f1273 := by
  apply lratCheckerSound f1273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1273
  · intro a ha; simp [p1273] at ha; subst a; trivial
  · exact checked1273
theorem derived1273 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1273 := by
  apply localUnsat_implies_entails f1273 [c108, c112, c1260, c822, c189, c7, c1270, c190, c8, c1272, c66, c61, c130, c153, c47, c45, c342, c347, c143, c1271, c308, c220, c227, c262, c256, c216] c1273 unsat1273 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1260 := derived1260 a h
  have h3 : Entails.eval a c822 := derived822 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c1270 := derived1270 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c1272 := derived1272 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c130 := h 129 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  have h18 : Entails.eval a c143 := h 142 (by decide)
  have h19 : Entails.eval a c1271 := derived1271 a h
  have h20 : Entails.eval a c308 := h 307 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c227 := h 226 (by decide)
  have h23 : Entails.eval a c262 := h 261 (by decide)
  have h24 : Entails.eval a c256 := h 255 (by decide)
  have h25 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1274 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1274 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c1003, some c7, some c123, some c121, some c36, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1274 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1274 : lratChecker f1274 p1274 = .success := by decide +kernel
theorem unsat1274 : Unsatisfiable (PosFin 57) f1274 := by
  apply lratCheckerSound f1274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1274
  · intro a ha; simp [p1274] at ha; subst a; trivial
  · exact checked1274
theorem derived1274 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1274 := by
  apply localUnsat_implies_entails f1274 [c195, c1003, c7, c123, c121, c36] c1274 unsat1274 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1275 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1275 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c112, some c108, some c1260, some c1268, some c1273, some c195, some c803, some c1274, some c199, some c66, some c61, some c152, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1275 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1275 : lratChecker f1275 p1275 = .success := by decide +kernel
theorem unsat1275 : Unsatisfiable (PosFin 57) f1275 := by
  apply lratCheckerSound f1275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1275
  · intro a ha; simp [p1275] at ha; subst a; trivial
  · exact checked1275
theorem derived1275 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1275 := by
  apply localUnsat_implies_entails f1275 [c106, c112, c108, c1260, c1268, c1273, c195, c803, c1274, c199, c66, c61, c152] c1275 unsat1275 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1260 := derived1260 a h
  have h4 : Entails.eval a c1268 := derived1268 a h
  have h5 : Entails.eval a c1273 := derived1273 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c803 := derived803 a h
  have h8 : Entails.eval a c1274 := derived1274 a h
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1276 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1276 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1275, some c131, some c150, some c50, some c45, some c57, some c58, some c137, some c274, some c42, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1276 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1276 : lratChecker f1276 p1276 = .success := by decide +kernel
theorem unsat1276 : Unsatisfiable (PosFin 57) f1276 := by
  apply lratCheckerSound f1276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1276
  · intro a ha; simp [p1276] at ha; subst a; trivial
  · exact checked1276
theorem derived1276 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1276 := by
  apply localUnsat_implies_entails f1276 [c1275, c131, c150, c50, c45, c57, c58, c137, c274, c42] c1276 unsat1276 (by rfl) a
  have h0 : Entails.eval a c1275 := derived1275 a h
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c150 := h 149 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1277 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1277 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1275, some c1276, some c66, some c61, some c130, some c149, some c47, some c45, some c58, some c138, some c274, some c41, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1277 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1277 : lratChecker f1277 p1277 = .success := by decide +kernel
theorem unsat1277 : Unsatisfiable (PosFin 57) f1277 := by
  apply lratCheckerSound f1277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1277
  · intro a ha; simp [p1277] at ha; subst a; trivial
  · exact checked1277
theorem derived1277 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1277 := by
  apply localUnsat_implies_entails f1277 [c1275, c1276, c66, c61, c130, c149, c47, c45, c58, c138, c274, c41] c1277 unsat1277 (by rfl) a
  have h0 : Entails.eval a c1275 := derived1275 a h
  have h1 : Entails.eval a c1276 := derived1276 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1278 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1278 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c193, some c17, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1278 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1278 : lratChecker f1278 p1278 = .success := by decide +kernel
theorem unsat1278 : Unsatisfiable (PosFin 57) f1278 := by
  apply lratCheckerSound f1278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1278
  · intro a ha; simp [p1278] at ha; subst a; trivial
  · exact checked1278
theorem derived1278 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1278 := by
  apply localUnsat_implies_entails f1278 [c194, c193, c17] c1278 unsat1278 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1279 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1279 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c154, some c58, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1279 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1279 : lratChecker f1279 p1279 = .success := by decide +kernel
theorem unsat1279 : Unsatisfiable (PosFin 57) f1279 := by
  apply lratCheckerSound f1279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1279
  · intro a ha; simp [p1279] at ha; subst a; trivial
  · exact checked1279
theorem derived1279 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1279 := by
  apply localUnsat_implies_entails f1279 [c150, c154, c58] c1279 unsat1279 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1280 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨35, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1280 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c66, some c50, some c45, some c268, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1280 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1280 : lratChecker f1280 p1280 = .success := by decide +kernel
theorem unsat1280 : Unsatisfiable (PosFin 57) f1280 := by
  apply lratCheckerSound f1280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1280
  · intro a ha; simp [p1280] at ha; subst a; trivial
  · exact checked1280
theorem derived1280 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1280 := by
  apply localUnsat_implies_entails f1280 [c61, c66, c50, c45, c268] c1280 unsat1280 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1281 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1281 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1275, some c106, some c108, some c1277, some c1278, some c1279, some c1280, some c138, some c142, some c42, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1281 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1281 : lratChecker f1281 p1281 = .success := by decide +kernel
theorem unsat1281 : Unsatisfiable (PosFin 57) f1281 := by
  apply lratCheckerSound f1281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1281
  · intro a ha; simp [p1281] at ha; subst a; trivial
  · exact checked1281
theorem derived1281 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1281 := by
  apply localUnsat_implies_entails f1281 [c1275, c106, c108, c1277, c1278, c1279, c1280, c138, c142, c42] c1281 unsat1281 (by rfl) a
  have h0 : Entails.eval a c1275 := derived1275 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c1279 := derived1279 a h
  have h6 : Entails.eval a c1280 := derived1280 a h
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1282 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1282 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c195, some c16, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1282 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1282 : lratChecker f1282 p1282 = .success := by decide +kernel
theorem unsat1282 : Unsatisfiable (PosFin 57) f1282 := by
  apply lratCheckerSound f1282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1282
  · intro a ha; simp [p1282] at ha; subst a; trivial
  · exact checked1282
theorem derived1282 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1282 := by
  apply localUnsat_implies_entails f1282 [c196, c195, c16] c1282 unsat1282 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1283 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1283 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1003, some c7, some c79, some c171, some c100, some c123, some c1274, some c36, some c17, some c928, some c263, some c249, some c260, some c176, some c180, some c89, some c28, some c80, some c695, some c372, some c232, some c368, some c709, some c229, some c244, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1283 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1283 : lratChecker f1283 p1283 = .success := by decide +kernel
theorem unsat1283 : Unsatisfiable (PosFin 57) f1283 := by
  apply lratCheckerSound f1283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1283
  · intro a ha; simp [p1283] at ha; subst a; trivial
  · exact checked1283
theorem derived1283 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1283 := by
  apply localUnsat_implies_entails f1283 [c1282, c1003, c7, c79, c171, c100, c123, c1274, c36, c17, c928, c263, c249, c260, c176, c180, c89, c28, c80, c695, c372, c232, c368, c709, c229, c244] c1283 unsat1283 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c1274 := derived1274 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c928 := derived928 a h
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c28 := h 27 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c695 := derived695 a h
  have h20 : Entails.eval a c372 := h 371 (by decide)
  have h21 : Entails.eval a c232 := h 231 (by decide)
  have h22 : Entails.eval a c368 := h 367 (by decide)
  have h23 : Entails.eval a c709 := derived709 a h
  have h24 : Entails.eval a c229 := h 228 (by decide)
  have h25 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1283

end CochromaticTwenty.Certificates.B16_2_2
