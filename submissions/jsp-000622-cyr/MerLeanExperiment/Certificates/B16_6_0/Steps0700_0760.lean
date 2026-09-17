import MerLeanExperiment.Certificates.B16_6_0.Steps0600_0699

/-! Generated from the actual pinned b16_6_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1097 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1048, some c1079, some c357, some c360, some c356, some c1092, some c267, some c265, some c1093, some c527, some c1089, some c1094, some c363, some c1095, some c73, some c81, some c339, some c343, some c1096, some c66, some c69, some c70, some c111, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 57) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c1006, c1048, c1079, c357, c360, c356, c1092, c267, c265, c1093, c527, c1089, c1094, c363, c1095, c73, c81, c339, c343, c1096, c66, c69, c70, c111] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c1079 := derived1079 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c1092 := derived1092 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c1093 := derived1093 a h
  have h10 : Entails.eval a c527 := derived527 a h
  have h11 : Entails.eval a c1089 := derived1089 a h
  have h12 : Entails.eval a c1094 := derived1094 a h
  have h13 : Entails.eval a c363 := h 362 (by decide)
  have h14 : Entails.eval a c1095 := derived1095 a h
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c81 := h 80 (by decide)
  have h17 : Entails.eval a c339 := h 338 (by decide)
  have h18 : Entails.eval a c343 := h 342 (by decide)
  have h19 : Entails.eval a c1096 := derived1096 a h
  have h20 : Entails.eval a c66 := h 65 (by decide)
  have h21 : Entails.eval a c69 := h 68 (by decide)
  have h22 : Entails.eval a c70 := h 69 (by decide)
  have h23 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨47, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c295, some c292, some c212, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 57) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c847, c295, c292, c212] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1099 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1006, some c1097, some c1079, some c379, some c377, some c169, some c121, some c267, some c265, some c927, some c1089, some c239, some c238, some c1098, some c140, some c249, some c250, some c373, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1099 : lratChecker f1099 p1099 = .success := by decide +kernel
theorem unsat1099 : Unsatisfiable (PosFin 57) f1099 := by
  apply lratCheckerSound f1099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1099
  · intro a ha; simp [p1099] at ha; subst a; trivial
  · exact checked1099
theorem derived1099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1099 := by
  apply localUnsat_implies_entails f1099 [c847, c1006, c1097, c1079, c379, c377, c169, c121, c267, c265, c927, c1089, c239, c238, c1098, c140, c249, c250, c373] c1099 unsat1099 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c1097 := derived1097 a h
  have h3 : Entails.eval a c1079 := derived1079 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c927 := derived927 a h
  have h11 : Entails.eval a c1089 := derived1089 a h
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c238 := h 237 (by decide)
  have h14 : Entails.eval a c1098 := derived1098 a h
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c249 := h 248 (by decide)
  have h17 : Entails.eval a c250 := h 249 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1100 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1048, some c847, some c1097, some c1099, some c217, some c54, some c20, some c265, some c267, some c249, some c76, some c527, some c328, some c363, some c329, some c385, some c931, some c21, some c250, some c78, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1100 : lratChecker f1100 p1100 = .success := by decide +kernel
theorem unsat1100 : Unsatisfiable (PosFin 57) f1100 := by
  apply lratCheckerSound f1100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1100
  · intro a ha; simp [p1100] at ha; subst a; trivial
  · exact checked1100
theorem derived1100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1100 := by
  apply localUnsat_implies_entails f1100 [c1006, c1048, c847, c1097, c1099, c217, c54, c20, c265, c267, c249, c76, c527, c328, c363, c329, c385, c931, c21, c250, c78] c1100 unsat1100 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c1097 := derived1097 a h
  have h4 : Entails.eval a c1099 := derived1099 a h
  have h5 : Entails.eval a c217 := h 216 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c249 := h 248 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c527 := derived527 a h
  have h13 : Entails.eval a c328 := h 327 (by decide)
  have h14 : Entails.eval a c363 := h 362 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c931 := derived931 a h
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c250 := h 249 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1101 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1048, some c847, some c1100, some c1097, some c1099, some c217, some c54, some c20, some c265, some c328, some c366, some c363, some c362, some c346, some c329, some c70, some c382, some c385, some c931, some c74, some c21, some c110, some c90, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1101 : lratChecker f1101 p1101 = .success := by decide +kernel
theorem unsat1101 : Unsatisfiable (PosFin 57) f1101 := by
  apply lratCheckerSound f1101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1101
  · intro a ha; simp [p1101] at ha; subst a; trivial
  · exact checked1101
theorem derived1101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1101 := by
  apply localUnsat_implies_entails f1101 [c1006, c1048, c847, c1100, c1097, c1099, c217, c54, c20, c265, c328, c366, c363, c362, c346, c329, c70, c382, c385, c931, c74, c21, c110, c90] c1101 unsat1101 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c1097 := derived1097 a h
  have h5 : Entails.eval a c1099 := derived1099 a h
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c366 := h 365 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c362 := h 361 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c382 := h 381 (by decide)
  have h18 : Entails.eval a c385 := h 384 (by decide)
  have h19 : Entails.eval a c931 := derived931 a h
  have h20 : Entails.eval a c74 := h 73 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c110 := h 109 (by decide)
  have h23 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1102 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c847, some c1097, some c1099, some c54, some c1100, some c217, some c20, some c267, some c265, some c1101, some c527, some c76, some c585, some c258, some c57, some c365, some c88, some c21, some c931, some c222, some c869, some c1049, some c230, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1102 : lratChecker f1102 p1102 = .success := by decide +kernel
theorem unsat1102 : Unsatisfiable (PosFin 57) f1102 := by
  apply lratCheckerSound f1102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1102
  · intro a ha; simp [p1102] at ha; subst a; trivial
  · exact checked1102
theorem derived1102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1102 := by
  apply localUnsat_implies_entails f1102 [c1006, c847, c1097, c1099, c54, c1100, c217, c20, c267, c265, c1101, c527, c76, c585, c258, c57, c365, c88, c21, c931, c222, c869, c1049, c230] c1102 unsat1102 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c1097 := derived1097 a h
  have h3 : Entails.eval a c1099 := derived1099 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c1100 := derived1100 a h
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c1101 := derived1101 a h
  have h11 : Entails.eval a c527 := derived527 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c585 := derived585 a h
  have h14 : Entails.eval a c258 := h 257 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c365 := h 364 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c931 := derived931 a h
  have h20 : Entails.eval a c222 := h 221 (by decide)
  have h21 : Entails.eval a c869 := derived869 a h
  have h22 : Entails.eval a c1049 := derived1049 a h
  have h23 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1103 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c847, some c1048, some c1097, some c1099, some c217, some c54, some c267, some c265, some c20, some c1100, some c1101, some c527, some c57, some c76, some c365, some c585, some c258, some c1102, some c385, some c329, some c361, some c230, some c266, some c1049, some c234, some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 57) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c1006, c847, c1048, c1097, c1099, c217, c54, c267, c265, c20, c1100, c1101, c527, c57, c76, c365, c585, c258, c1102, c385, c329, c361, c230, c266, c1049, c234] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c1048 := derived1048 a h
  have h3 : Entails.eval a c1097 := derived1097 a h
  have h4 : Entails.eval a c1099 := derived1099 a h
  have h5 : Entails.eval a c217 := h 216 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c1100 := derived1100 a h
  have h11 : Entails.eval a c1101 := derived1101 a h
  have h12 : Entails.eval a c527 := derived527 a h
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c365 := h 364 (by decide)
  have h16 : Entails.eval a c585 := derived585 a h
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c1102 := derived1102 a h
  have h19 : Entails.eval a c385 := h 384 (by decide)
  have h20 : Entails.eval a c329 := h 328 (by decide)
  have h21 : Entails.eval a c361 := h 360 (by decide)
  have h22 : Entails.eval a c230 := h 229 (by decide)
  have h23 : Entails.eval a c266 := h 265 (by decide)
  have h24 : Entails.eval a c1049 := derived1049 a h
  have h25 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1048, some c847, some c1006, some c217, some c267, some c223, some c127, some c20, some c57, some c76, some c362, some c249, some c585, some c258, some c328, some c125, some c181, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 57) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c1103, c1048, c847, c1006, c217, c267, c223, c127, c20, c57, c76, c362, c249, c585, c258, c328, c125, c181] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c1006 := derived1006 a h
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c362 := h 361 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c585 := derived585 a h
  have h14 : Entails.eval a c258 := h 257 (by decide)
  have h15 : Entails.eval a c328 := h 327 (by decide)
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1048, some c1103, some c847, some c217, some c267, some c265, some c20, some c1104, some c527, some c328, some c363, some c362, some c329, some c70, some c235, some c382, some c385, some c931, some c34, some c83, some c90, some c110, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 57) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c1006, c1048, c1103, c847, c217, c267, c265, c20, c1104, c527, c328, c363, c362, c329, c70, c235, c382, c385, c931, c34, c83, c90, c110] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c847 := derived847 a h
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c1104 := derived1104 a h
  have h9 : Entails.eval a c527 := derived527 a h
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c382 := h 381 (by decide)
  have h17 : Entails.eval a c385 := h 384 (by decide)
  have h18 : Entails.eval a c931 := derived931 a h
  have h19 : Entails.eval a c34 := h 33 (by decide)
  have h20 : Entails.eval a c83 := h 82 (by decide)
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1006, some c377, some c379, some c267, some c265, some c20, some c1089, some c238, some c88, some c21, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 57) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c847, c1006, c377, c379, c267, c265, c20, c1089, c238, c88, c21] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1089 := derived1089 a h
  have h8 : Entails.eval a c238 := h 237 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1105, some c1106, some c121, some c1054, some c225, some c127, some c920, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 57) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c1103, c1105, c1106, c121, c1054, c225, c127, c920] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1105 := derived1105 a h
  have h2 : Entails.eval a c1106 := derived1106 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c1054 := derived1054 a h
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c920 := derived920 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨35, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨42, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c24, some c3, some c74, some c643, some c253, some c189, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 57) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c1006, c24, c3, c74, c643, c253, c189] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c643 := derived643 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1109 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1048, some c1006, some c847, some c1105, some c377, some c1106, some c121, some c169, some c1107, some c362, some c1060, some c1063, some c123, some c115, some c279, some c1108, some c400, some c57, some c253, some c344, some c944, some c189, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 57) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c1048, c1006, c847, c1105, c377, c1106, c121, c169, c1107, c362, c1060, c1063, c123, c115, c279, c1108, c400, c57, c253, c344, c944, c189] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c1105 := derived1105 a h
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c1106 := derived1106 a h
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c1107 := derived1107 a h
  have h9 : Entails.eval a c362 := h 361 (by decide)
  have h10 : Entails.eval a c1060 := derived1060 a h
  have h11 : Entails.eval a c1063 := derived1063 a h
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c279 := h 278 (by decide)
  have h15 : Entails.eval a c1108 := derived1108 a h
  have h16 : Entails.eval a c400 := derived400 a h
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c344 := h 343 (by decide)
  have h20 : Entails.eval a c944 := derived944 a h
  have h21 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1110 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨17, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1006, some c1048, some c1109, some c54, some c121, some c169, some c377, some c379, some c1060, some c1063, some c123, some c270, some c1051, some c361, some c134, some c226, some c63, some c26, some c74, some c83, some c643, some c253, some c346, some c111, some c189, some c96, some c97, some c12, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 57) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c847, c1006, c1048, c1109, c54, c121, c169, c377, c379, c1060, c1063, c123, c270, c1051, c361, c134, c226, c63, c26, c74, c83, c643, c253, c346, c111, c189, c96, c97, c12] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c1048 := derived1048 a h
  have h3 : Entails.eval a c1109 := derived1109 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c1060 := derived1060 a h
  have h10 : Entails.eval a c1063 := derived1063 a h
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c1051 := derived1051 a h
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c226 := h 225 (by decide)
  have h17 : Entails.eval a c63 := h 62 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c74 := h 73 (by decide)
  have h20 : Entails.eval a c83 := h 82 (by decide)
  have h21 : Entails.eval a c643 := derived643 a h
  have h22 : Entails.eval a c253 := h 252 (by decide)
  have h23 : Entails.eval a c346 := h 345 (by decide)
  have h24 : Entails.eval a c111 := h 110 (by decide)
  have h25 : Entails.eval a c189 := h 188 (by decide)
  have h26 : Entails.eval a c96 := h 95 (by decide)
  have h27 : Entails.eval a c97 := h 96 (by decide)
  have h28 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1111 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1048, some c1103, some c1109, some c54, some c121, some c1110, some c362, some c1054, some c225, some c127, some c920, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 57) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c1048, c1103, c1109, c54, c121, c1110, c362, c1054, c225, c127, c920] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1109 := derived1109 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c1110 := derived1110 a h
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c1054 := derived1054 a h
  have h8 : Entails.eval a c225 := h 224 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c920 := derived920 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1103, some c847, some c54, some c379, some c377, some c1111, some c267, some c265, some c927, some c1089, some c127, some c223, some c238, some c172, some c1098, some c140, some c249, some c250, some c373, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 57) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c1006, c1103, c847, c54, c379, c377, c1111, c267, c265, c927, c1089, c127, c223, c238, c172, c1098, c140, c249, c250, c373] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c1111 := derived1111 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c927 := derived927 a h
  have h10 : Entails.eval a c1089 := derived1089 a h
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c223 := h 222 (by decide)
  have h13 : Entails.eval a c238 := h 237 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c1098 := derived1098 a h
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c249 := h 248 (by decide)
  have h18 : Entails.eval a c250 := h 249 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1109, some c1112, some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 57) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c1109, c1112] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c1109 := derived1109 a h
  have h1 : Entails.eval a c1112 := derived1112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1114 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1113, some c1048, some c357, some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p1114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 57) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c1113, c1048, c357] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c1113 := derived1113 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1113, some c1048, some c356, some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 57) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c1113, c1048, c356] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c1113 := derived1113 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1113, some c1048, some c1114, some c1006, some c1115, some c1103, some c847, some c267, some c231, some c927, some c1073, some c73, some c248, some c339, some c265, some c266, some c931, some c82, some c223, some c127, some c238, some c74, some c183, some c108, some c118, some c37, some c300, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 57) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c1113, c1048, c1114, c1006, c1115, c1103, c847, c267, c231, c927, c1073, c73, c248, c339, c265, c266, c931, c82, c223, c127, c238, c74, c183, c108, c118, c37, c300] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c1113 := derived1113 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c1114 := derived1114 a h
  have h3 : Entails.eval a c1006 := derived1006 a h
  have h4 : Entails.eval a c1115 := derived1115 a h
  have h5 : Entails.eval a c1103 := derived1103 a h
  have h6 : Entails.eval a c847 := derived847 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c927 := derived927 a h
  have h10 : Entails.eval a c1073 := derived1073 a h
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c339 := h 338 (by decide)
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c931 := derived931 a h
  have h17 : Entails.eval a c82 := h 81 (by decide)
  have h18 : Entails.eval a c223 := h 222 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c238 := h 237 (by decide)
  have h21 : Entails.eval a c74 := h 73 (by decide)
  have h22 : Entails.eval a c183 := h 182 (by decide)
  have h23 : Entails.eval a c108 := h 107 (by decide)
  have h24 : Entails.eval a c118 := h 117 (by decide)
  have h25 : Entails.eval a c37 := h 36 (by decide)
  have h26 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1114, some c1006, some c1115, some c1103, some c847, some c1116, some c267, some c231, some c927, some c1073, some c73, some c248, some c266, some c223, some c127, some c265, some c183, some c118, some c131, some c300, some c173, some c142, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 57) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c1114, c1006, c1115, c1103, c847, c1116, c267, c231, c927, c1073, c73, c248, c266, c223, c127, c265, c183, c118, c131, c300, c173, c142] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c1114 := derived1114 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c1103 := derived1103 a h
  have h4 : Entails.eval a c847 := derived847 a h
  have h5 : Entails.eval a c1116 := derived1116 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c231 := h 230 (by decide)
  have h8 : Entails.eval a c927 := derived927 a h
  have h9 : Entails.eval a c1073 := derived1073 a h
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c223 := h 222 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c118 := h 117 (by decide)
  have h18 : Entails.eval a c131 := h 130 (by decide)
  have h19 : Entails.eval a c300 := h 299 (by decide)
  have h20 : Entails.eval a c173 := h 172 (by decide)
  have h21 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1114, some c1006, some c1113, some c1115, some c1103, some c267, some c265, some c127, some c231, some c266, some c927, some c1073, some c931, some c73, some c82, some c249, some c1117, some c222, some c342, some c373, some c78, some c905, some c111, some c192, some c68, some c16, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 57) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c1114, c1006, c1113, c1115, c1103, c267, c265, c127, c231, c266, c927, c1073, c931, c73, c82, c249, c1117, c222, c342, c373, c78, c905, c111, c192, c68, c16] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c1114 := derived1114 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c1113 := derived1113 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1103 := derived1103 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c927 := derived927 a h
  have h11 : Entails.eval a c1073 := derived1073 a h
  have h12 : Entails.eval a c931 := derived931 a h
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c249 := h 248 (by decide)
  have h16 : Entails.eval a c1117 := derived1117 a h
  have h17 : Entails.eval a c222 := h 221 (by decide)
  have h18 : Entails.eval a c342 := h 341 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c905 := derived905 a h
  have h22 : Entails.eval a c111 := h 110 (by decide)
  have h23 : Entails.eval a c192 := h 191 (by decide)
  have h24 : Entails.eval a c68 := h 67 (by decide)
  have h25 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨38, by decide⟩, false), (⟨22, by decide⟩, true), (⟨42, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1113, some c1114, some c1115, some c1118, some c114, some c208, some c173, some c277, some c161, some c113, some c199, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 57) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c847, c1113, c1114, c1115, c1118, c114, c208, c173, c277, c161, c113, c199] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1113 := derived1113 a h
  have h2 : Entails.eval a c1114 := derived1114 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1118 := derived1118 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c196, some c131, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 57) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c198, c196, c131] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨22, by decide⟩, true), (⟨15, by decide⟩, false), (⟨42, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1115, some c1114, some c1118, some c1113, some c1048, some c1119, some c274, some c113, some c199, some c1120, some c161, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 57) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c1115, c1114, c1118, c1113, c1048, c1119, c274, c113, c199, c1120, c161] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c1114 := derived1114 a h
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c1113 := derived1113 a h
  have h4 : Entails.eval a c1048 := derived1048 a h
  have h5 : Entails.eval a c1119 := derived1119 a h
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c1120 := derived1120 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c222, some c1121, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 57) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c222, c1121] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c222 := h 221 (by decide)
  have h1 : Entails.eval a c1121 := derived1121 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1123 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1103, some c1006, some c1118, some c1115, some c1114, some c1048, some c382, some c231, some c273, some c951, some c230, some c336, some c363, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 57) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c847, c1103, c1006, c1118, c1115, c1114, c1048, c382, c231, c273, c951, c230, c336, c363] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1006 := derived1006 a h
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c1115 := derived1115 a h
  have h5 : Entails.eval a c1114 := derived1114 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c951 := derived951 a h
  have h11 : Entails.eval a c230 := h 229 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1118, some c1006, some c1103, some c1115, some c1114, some c847, some c1121, some c1122, some c126, some c177, some c200, some c183, some c161, some c223, some c205, some c273, some c129, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 57) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c1118, c1006, c1103, c1115, c1114, c847, c1121, c1122, c126, c177, c200, c183, c161, c223, c205, c273, c129] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c1118 := derived1118 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c847 := derived847 a h
  have h6 : Entails.eval a c1121 := derived1121 a h
  have h7 : Entails.eval a c1122 := derived1122 a h
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c177 := h 176 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c161 := h 160 (by decide)
  have h13 : Entails.eval a c223 := h 222 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1118, some c377, some c382, some c237, some c1123, some c272, some c1124, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 57) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c847, c1118, c377, c382, c237, c1123, c272, c1124] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c1123 := derived1123 a h
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c1124 := derived1124 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨21, by decide⟩, true), (⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1048, some c1103, some c126, some c234, some c183, some c363, some c338, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 57) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c1048, c1103, c126, c234, c183, c363, c338] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c234 := h 233 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨46, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1114, some c1115, some c1118, some c177, some c200, some c161, some c129, some c205, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 57) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c847, c1114, c1115, c1118, c177, c200, c161, c129, c205] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1114 := derived1114 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c177 := h 176 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1113, some c1118, some c1114, some c1115, some c1125, some c238, some c931, some c1126, some c1127, some c118, some c138, some c277, some c205, some c113, some c161, some c1120, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 57) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c1113, c1118, c1114, c1115, c1125, c238, c931, c1126, c1127, c118, c138, c277, c205, c113, c161, c1120] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c1113 := derived1113 a h
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c1114 := derived1114 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c238 := h 237 (by decide)
  have h6 : Entails.eval a c931 := derived931 a h
  have h7 : Entails.eval a c1126 := derived1126 a h
  have h8 : Entails.eval a c1127 := derived1127 a h
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c277 := h 276 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c1120 := derived1120 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1103, some c1113, some c1118, some c1114, some c1115, some c1125, some c238, some c1128, some c273, some c223, some c183, some c118, some c126, some c277, some c113, some c199, some c1120, some c161, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 57) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c1006, c1103, c1113, c1118, c1114, c1115, c1125, c238, c1128, c273, c223, c183, c118, c126, c277, c113, c199, c1120, c161] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1113 := derived1113 a h
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c1115 := derived1115 a h
  have h6 : Entails.eval a c1125 := derived1125 a h
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c1128 := derived1128 a h
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c223 := h 222 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c126 := h 125 (by decide)
  have h14 : Entails.eval a c277 := h 276 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c1120 := derived1120 a h
  have h18 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1118, some c847, some c1048, some c1115, some c1114, some c1103, some c1113, some c231, some c272, some c620, some c235, some c363, some c941, some c27, some c59, some c83, some c78, some c103, some c108, some c342, some c355, some c93, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p1130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 57) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c1118, c847, c1048, c1115, c1114, c1103, c1113, c231, c272, c620, c235, c363, c941, c27, c59, c83, c78, c103, c108, c342, c355, c93] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c1118 := derived1118 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c1048 := derived1048 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c1103 := derived1103 a h
  have h6 : Entails.eval a c1113 := derived1113 a h
  have h7 : Entails.eval a c231 := h 230 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c620 := derived620 a h
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c941 := derived941 a h
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c108 := h 107 (by decide)
  have h19 : Entails.eval a c342 := h 341 (by decide)
  have h20 : Entails.eval a c355 := h 354 (by decide)
  have h21 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1114, some c1115, some c1103, some c1113, some c1006, some c1125, some c1129, some c1130, some c273, some c941, some c230, some c221, some c125, some c27, some c181, some c83, some c78, some c60, some c103, some c342, some c30, some c73, some c599, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 57) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c1114, c1115, c1103, c1113, c1006, c1125, c1129, c1130, c273, c941, c230, c221, c125, c27, c181, c83, c78, c60, c103, c342, c30, c73, c599] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c1114 := derived1114 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c1113 := derived1113 a h
  have h4 : Entails.eval a c1006 := derived1006 a h
  have h5 : Entails.eval a c1125 := derived1125 a h
  have h6 : Entails.eval a c1129 := derived1129 a h
  have h7 : Entails.eval a c1130 := derived1130 a h
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c941 := derived941 a h
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c342 := h 341 (by decide)
  have h20 : Entails.eval a c30 := h 29 (by decide)
  have h21 : Entails.eval a c73 := h 72 (by decide)
  have h22 : Entails.eval a c599 := derived599 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1118, some c205, some c199, some c129, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 57) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c1118, c205, c199, c129] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c1118 := derived1118 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1115, some c1114, some c1113, some c1048, some c1118, some c161, some c363, some c165, some c201, some c114, some c274, some c281, some c206, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 57) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c1115, c1114, c1113, c1048, c1118, c161, c363, c165, c201, c114, c274, c281, c206] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c1114 := derived1114 a h
  have h2 : Entails.eval a c1113 := derived1113 a h
  have h3 : Entails.eval a c1048 := derived1048 a h
  have h4 : Entails.eval a c1118 := derived1118 a h
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1114, some c1006, some c1115, some c1125, some c1129, some c1130, some c273, some c1132, some c1133, some c230, some c941, some c27, some c1131, some c59, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 57) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c1103, c1114, c1006, c1115, c1125, c1129, c1130, c273, c1132, c1133, c230, c941, c27, c1131, c59] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1114 := derived1114 a h
  have h2 : Entails.eval a c1006 := derived1006 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1129 := derived1129 a h
  have h6 : Entails.eval a c1130 := derived1130 a h
  have h7 : Entails.eval a c273 := h 272 (by decide)
  have h8 : Entails.eval a c1132 := derived1132 a h
  have h9 : Entails.eval a c1133 := derived1133 a h
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c941 := derived941 a h
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c1131 := derived1131 a h
  have h14 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1118, some c1115, some c1006, some c1125, some c1129, some c1130, some c273, some c1132, some c1133, some c230, some c272, some c1134, some c620, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 57) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c847, c1118, c1115, c1006, c1125, c1129, c1130, c273, c1132, c1133, c230, c272, c1134, c620] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c1006 := derived1006 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1129 := derived1129 a h
  have h6 : Entails.eval a c1130 := derived1130 a h
  have h7 : Entails.eval a c273 := h 272 (by decide)
  have h8 : Entails.eval a c1132 := derived1132 a h
  have h9 : Entails.eval a c1133 := derived1133 a h
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c1134 := derived1134 a h
  have h13 : Entails.eval a c620 := derived620 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1006, some c1115, some c847, some c1103, some c1114, some c1118, some c1135, some c270, some c1132, some c161, some c165, some c178, some c338, some c336, some c380, some c386, some c236, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 57) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c1006, c1115, c847, c1103, c1114, c1118, c1135, c270, c1132, c161, c165, c178, c338, c336, c380, c386, c236] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c1006 := derived1006 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c1103 := derived1103 a h
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c1135 := derived1135 a h
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c1132 := derived1132 a h
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  have h11 : Entails.eval a c178 := h 177 (by decide)
  have h12 : Entails.eval a c338 := h 337 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c386 := h 385 (by decide)
  have h16 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1115, some c1048, some c1103, some c1118, some c1006, some c847, some c1114, some c1135, some c270, some c1132, some c161, some c1136, some c363, some c941, some c230, some c221, some c125, some c23, some c910, some c181, some c377, some c169, some c60, some c223, some c74, some c113, some c30, some c253, some c252, some c397, some c57, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 57) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c1115, c1048, c1103, c1118, c1006, c847, c1114, c1135, c270, c1132, c161, c1136, c363, c941, c230, c221, c125, c23, c910, c181, c377, c169, c60, c223, c74, c113, c30, c253, c252, c397, c57] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c1006 := derived1006 a h
  have h5 : Entails.eval a c847 := derived847 a h
  have h6 : Entails.eval a c1114 := derived1114 a h
  have h7 : Entails.eval a c1135 := derived1135 a h
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c1132 := derived1132 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c1136 := derived1136 a h
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c941 := derived941 a h
  have h14 : Entails.eval a c230 := h 229 (by decide)
  have h15 : Entails.eval a c221 := h 220 (by decide)
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c910 := derived910 a h
  have h19 : Entails.eval a c181 := h 180 (by decide)
  have h20 : Entails.eval a c377 := h 376 (by decide)
  have h21 : Entails.eval a c169 := h 168 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  have h23 : Entails.eval a c223 := h 222 (by decide)
  have h24 : Entails.eval a c74 := h 73 (by decide)
  have h25 : Entails.eval a c113 := h 112 (by decide)
  have h26 : Entails.eval a c30 := h 29 (by decide)
  have h27 : Entails.eval a c253 := h 252 (by decide)
  have h28 : Entails.eval a c252 := h 251 (by decide)
  have h29 : Entails.eval a c397 := derived397 a h
  have h30 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1137, some c1103, some c127, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 57) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c1137, c1103, c127] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c1137 := derived1137 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1137, some c1115, some c1103, some c163, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 57) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c1137, c1115, c1103, c163] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c1137 := derived1137 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1138, some c1006, some c273, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 57) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c1138, c1006, c273] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c1138 := derived1138 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1006, some c1138, some c1114, some c1118, some c1139, some c1048, some c1113, some c60, some c30, some c57, some c599, some c1023, some c339, some c38, some c369, some c554, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 57) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c1103, c1006, c1138, c1114, c1118, c1139, c1048, c1113, c60, c30, c57, c599, c1023, c339, c38, c369, c554] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1006 := derived1006 a h
  have h2 : Entails.eval a c1138 := derived1138 a h
  have h3 : Entails.eval a c1114 := derived1114 a h
  have h4 : Entails.eval a c1118 := derived1118 a h
  have h5 : Entails.eval a c1139 := derived1139 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c1113 := derived1113 a h
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c599 := derived599 a h
  have h12 : Entails.eval a c1023 := derived1023 a h
  have h13 : Entails.eval a c339 := h 338 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c554 := derived554 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1048, some c1113, some c847, some c339, some c74, some c369, some c103, some c108, some c391, some c608, some c368, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 57) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c1048, c1113, c847, c339, c74, c369, c103, c108, c391, c608, c368] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c1113 := derived1113 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c391 := h 390 (by decide)
  have h9 : Entails.eval a c608 := derived608 a h
  have h10 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1140, some c1103, some c1138, some c1006, some c1139, some c1118, some c1048, some c1114, some c1113, some c1115, some c221, some c941, some c60, some c30, some c57, some c383, some c1141, some c1142, some c73, some c2, some c113, some c274, some c915, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 57) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c1140, c1103, c1138, c1006, c1139, c1118, c1048, c1114, c1113, c1115, c221, c941, c60, c30, c57, c383, c1141, c1142, c73, c2, c113, c274, c915] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1138 := derived1138 a h
  have h3 : Entails.eval a c1006 := derived1006 a h
  have h4 : Entails.eval a c1139 := derived1139 a h
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c1114 := derived1114 a h
  have h8 : Entails.eval a c1113 := derived1113 a h
  have h9 : Entails.eval a c1115 := derived1115 a h
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c941 := derived941 a h
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c383 := h 382 (by decide)
  have h16 : Entails.eval a c1141 := derived1141 a h
  have h17 : Entails.eval a c1142 := derived1142 a h
  have h18 : Entails.eval a c73 := h 72 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c274 := h 273 (by decide)
  have h22 : Entails.eval a c915 := derived915 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1115, some c1140, some c1114, some c1006, some c1138, some c1048, some c847, some c221, some c1143, some c386, some c57, some c30, some c941, some c105, some c103, some c715, some c74, some c83, some c347, some c385, some c367, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 57) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c1103, c1115, c1140, c1114, c1006, c1138, c1048, c847, c221, c1143, c386, c57, c30, c941, c105, c103, c715, c74, c83, c347, c385, c367] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1114 := derived1114 a h
  have h4 : Entails.eval a c1006 := derived1006 a h
  have h5 : Entails.eval a c1138 := derived1138 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c847 := derived847 a h
  have h8 : Entails.eval a c221 := h 220 (by decide)
  have h9 : Entails.eval a c1143 := derived1143 a h
  have h10 : Entails.eval a c386 := h 385 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c941 := derived941 a h
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c715 := derived715 a h
  have h17 : Entails.eval a c74 := h 73 (by decide)
  have h18 : Entails.eval a c83 := h 82 (by decide)
  have h19 : Entails.eval a c347 := h 346 (by decide)
  have h20 : Entails.eval a c385 := h 384 (by decide)
  have h21 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1115, some c1140, some c1114, some c1006, some c1138, some c1048, some c1113, some c1137, some c1139, some c221, some c1143, some c386, some c57, some c30, some c941, some c1144, some c73, some c35, some c274, some c295, some c151, some c46, some c6, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 57) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1103, c1115, c1140, c1114, c1006, c1138, c1048, c1113, c1137, c1139, c221, c1143, c386, c57, c30, c941, c1144, c73, c35, c274, c295, c151, c46, c6] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1114 := derived1114 a h
  have h4 : Entails.eval a c1006 := derived1006 a h
  have h5 : Entails.eval a c1138 := derived1138 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c1113 := derived1113 a h
  have h8 : Entails.eval a c1137 := derived1137 a h
  have h9 : Entails.eval a c1139 := derived1139 a h
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c1143 := derived1143 a h
  have h12 : Entails.eval a c386 := h 385 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c941 := derived941 a h
  have h16 : Entails.eval a c1144 := derived1144 a h
  have h17 : Entails.eval a c73 := h 72 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c274 := h 273 (by decide)
  have h20 : Entails.eval a c295 := h 294 (by decide)
  have h21 : Entails.eval a c151 := h 150 (by decide)
  have h22 : Entails.eval a c46 := h 45 (by decide)
  have h23 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c1114, some c1115, some c1048, some c1113, some c1139, some c847, some c1137, some c941, some c1145, some c339, some c74, some c103, some c108, some c6, some c608, some c188, some c368, some c391, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 57) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1103, c1114, c1115, c1048, c1113, c1139, c847, c1137, c941, c1145, c339, c74, c103, c108, c6, c608, c188, c368, c391] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c1114 := derived1114 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c1048 := derived1048 a h
  have h4 : Entails.eval a c1113 := derived1113 a h
  have h5 : Entails.eval a c1139 := derived1139 a h
  have h6 : Entails.eval a c847 := derived847 a h
  have h7 : Entails.eval a c1137 := derived1137 a h
  have h8 : Entails.eval a c941 := derived941 a h
  have h9 : Entails.eval a c1145 := derived1145 a h
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c608 := derived608 a h
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c368 := h 367 (by decide)
  have h18 : Entails.eval a c391 := h 390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1140, some c1115, some c847, some c1048, some c1113, some c1139, some c1118, some c230, some c1146, some c377, some c382, some c173, some c910, some c237, some c114, some c272, some c274, some c1120, some c113, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 57) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c1140, c1115, c847, c1048, c1113, c1139, c1118, c230, c1146, c377, c382, c173, c910, c237, c114, c272, c274, c1120, c113] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c1048 := derived1048 a h
  have h4 : Entails.eval a c1113 := derived1113 a h
  have h5 : Entails.eval a c1139 := derived1139 a h
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c230 := h 229 (by decide)
  have h8 : Entails.eval a c1146 := derived1146 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c173 := h 172 (by decide)
  have h12 : Entails.eval a c910 := derived910 a h
  have h13 : Entails.eval a c237 := h 236 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c274 := h 273 (by decide)
  have h17 : Entails.eval a c1120 := derived1120 a h
  have h18 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c1139, some c1137, some c1103, some c1114, some c336, some c167, some c178, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 57) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c847, c1139, c1137, c1103, c1114, c336, c167, c178] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c1139 := derived1139 a h
  have h2 : Entails.eval a c1137 := derived1137 a h
  have h3 : Entails.eval a c1103 := derived1103 a h
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1140, some c221, some c1143, some c386, some c1147, some c1148, some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 57) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c1140, c221, c1143, c386, c1147, c1148] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c386 := h 385 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c1148 := derived1148 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1149, some c1048, some c363, some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 57) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1149, c1048, c363] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1149 := derived1149 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1150, some c1137, some c1103, some c167, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 57) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1150, c1137, c1103, c167] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1150 := derived1150 a h
  have h1 : Entails.eval a c1137 := derived1137 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1150, some c1148, some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p1152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 57) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c1150, c1148] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c1150 := derived1150 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1153 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1151, some c847, some c1139, some c178, some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 57) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1151, c847, c1139, c178] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1151 := derived1151 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c1139 := derived1139 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1153, some c1103, some c1150, some c338, some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 57) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c1153, c1103, c1150, c338] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1150 := derived1150 a h
  have h3 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1154, some c1152, some c386, some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p1155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 57) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1154, c1152, c386] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1154 := derived1154 a h
  have h1 : Entails.eval a c1152 := derived1152 a h
  have h2 : Entails.eval a c386 := h 385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1154, some c1152, some c380, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 57) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c1154, c1152, c380] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c1154 := derived1154 a h
  have h1 : Entails.eval a c1152 := derived1152 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1155, some c1156, some c1140, some c1118, some c236]
def p1157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 57) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c1155, c1156, c1140, c1118, c236] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c1155 := derived1155 a h
  have h1 : Entails.eval a c1156 := derived1156 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1157

end CochromaticTwenty.Certificates.B16_6_0
