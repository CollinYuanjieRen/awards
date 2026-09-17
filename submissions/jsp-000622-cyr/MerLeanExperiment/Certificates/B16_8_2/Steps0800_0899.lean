import MerLeanExperiment.Certificates.B16_8_2.Steps0700_0799

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1181 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c195, some c283, some c275, some c42, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 57) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c315, c195, c283, c275, c42] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c75, some c368, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 57) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c73, c75, c368] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, false), (⟨33, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1179, some c1182, some c86, some c373, some c1181, some c1180, some c89, some c92, some c377, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p1183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 57) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1179, c1182, c86, c373, c1181, c1180, c89, c92, c377] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1182 := derived1182 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c1181 := derived1181 a h
  have h5 : Entails.eval a c1180 := derived1180 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1184 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1153, some c1138, some c151, some c1118, some c372, some c1165, some c1178, some c156, some c72, some c363, some c182, some c102, some c174, some c1179, some c1182, some c315, some c1183, some c104, some c867, some c57, some c39, some c60, some c349, some c348, some c283, some c266, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 57) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1153, c1138, c151, c1118, c372, c1165, c1178, c156, c72, c363, c182, c102, c174, c1179, c1182, c315, c1183, c104, c867, c57, c39, c60, c349, c348, c283, c266] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1138 := derived1138 a h
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c1165 := derived1165 a h
  have h6 : Entails.eval a c1178 := derived1178 a h
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c182 := h 181 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c1179 := derived1179 a h
  have h14 : Entails.eval a c1182 := derived1182 a h
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c1183 := derived1183 a h
  have h17 : Entails.eval a c104 := h 103 (by decide)
  have h18 : Entails.eval a c867 := derived867 a h
  have h19 : Entails.eval a c57 := h 56 (by decide)
  have h20 : Entails.eval a c39 := h 38 (by decide)
  have h21 : Entails.eval a c60 := h 59 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  have h23 : Entails.eval a c348 := h 347 (by decide)
  have h24 : Entails.eval a c283 := h 282 (by decide)
  have h25 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨26, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c136, some c124, some c267, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 57) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c136, c124, c267] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c83, some c102, some c76, some c957, some c317, some c976, some c181, some c133, some c37, some c117, some c41, some c277, some c191, some c231, some c225, some c109, some c1185, some c165, some c185, some c138, some c128, some c116, some c192, some c43, some c29, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 57) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c372, c83, c102, c76, c957, c317, c976, c181, c133, c37, c117, c41, c277, c191, c231, c225, c109, c1185, c165, c185, c138, c128, c116, c192, c43, c29] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c957 := derived957 a h
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c976 := derived976 a h
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c277 := h 276 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c231 := h 230 (by decide)
  have h15 : Entails.eval a c225 := h 224 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c1185 := derived1185 a h
  have h18 : Entails.eval a c165 := h 164 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c138 := h 137 (by decide)
  have h21 : Entails.eval a c128 := h 127 (by decide)
  have h22 : Entails.eval a c116 := h 115 (by decide)
  have h23 : Entails.eval a c192 := h 191 (by decide)
  have h24 : Entails.eval a c43 := h 42 (by decide)
  have h25 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨33, by decide⟩, true), (⟨34, by decide⟩, false), (⟨44, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c156, some c165, some c138, some c55, some c863, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 57) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c37, c156, c165, c138, c55, c863] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c863 := derived863 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1138, some c151, some c1118, some c372, some c181, some c1153, some c1184, some c83, some c102, some c976, some c76, some c957, some c317, some c1186, some c33, some c117, some c44, some c277, some c191, some c231, some c225, some c109, some c1187, some c140, some c124, some c267, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 57) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c1138, c151, c1118, c372, c181, c1153, c1184, c83, c102, c976, c76, c957, c317, c1186, c33, c117, c44, c277, c191, c231, c225, c109, c1187, c140, c124, c267] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c1138 := derived1138 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c1153 := derived1153 a h
  have h6 : Entails.eval a c1184 := derived1184 a h
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c976 := derived976 a h
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c957 := derived957 a h
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c1186 := derived1186 a h
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  have h19 : Entails.eval a c231 := h 230 (by decide)
  have h20 : Entails.eval a c225 := h 224 (by decide)
  have h21 : Entails.eval a c109 := h 108 (by decide)
  have h22 : Entails.eval a c1187 := derived1187 a h
  have h23 : Entails.eval a c140 := h 139 (by decide)
  have h24 : Entails.eval a c124 := h 123 (by decide)
  have h25 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨25, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c976, some c950, some c361, some c85, some c377, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 57) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c976, c950, c361, c85, c377] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c976 := derived976 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨33, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c1188, some c167, some c183, some c182, some c116, some c1138, some c53, some c33, some c120, some c174, some c153, some c40, some c196, some c1155, some c251, some c1189, some c1144, some c1163, some c54, some c978, some c317, some c1142, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 57) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c151, c1118, c372, c1188, c167, c183, c182, c116, c1138, c53, c33, c120, c174, c153, c40, c196, c1155, c251, c1189, c1144, c1163, c54, c978, c317, c1142] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1188 := derived1188 a h
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c1138 := derived1138 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  have h16 : Entails.eval a c1155 := derived1155 a h
  have h17 : Entails.eval a c251 := h 250 (by decide)
  have h18 : Entails.eval a c1189 := derived1189 a h
  have h19 : Entails.eval a c1144 := derived1144 a h
  have h20 : Entails.eval a c1163 := derived1163 a h
  have h21 : Entails.eval a c54 := h 53 (by decide)
  have h22 : Entails.eval a c978 := derived978 a h
  have h23 : Entails.eval a c317 := h 316 (by decide)
  have h24 : Entails.eval a c1142 := derived1142 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨33, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1138, some c53, some c151, some c1118, some c372, some c1188, some c167, some c182, some c183, some c116, some c1190, some c140, some c160, some c420, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 57) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c1138, c53, c151, c1118, c372, c1188, c167, c182, c183, c116, c1190, c140, c160, c420] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c1138 := derived1138 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c1188 := derived1188 a h
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c182 := h 181 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c1190 := derived1190 a h
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c160 := h 159 (by decide)
  have h13 : Entails.eval a c420 := derived420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨46, by decide⟩, false), (⟨13, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c227, some c317, some c108, some c210, some c253, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 57) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c160, c227, c317, c108, c210, c253] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c227 := h 226 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c210 := h 209 (by decide)
  have h5 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨33, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c1188, some c167, some c1138, some c33, some c120, some c182, some c166, some c174, some c153, some c53, some c1191, some c231, some c110, some c1192, some c140, some c40, some c196, some c32, some c251, some c31, some c1189, some c1144, some c1163, some c1125, some c290, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 57) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c151, c1118, c372, c1188, c167, c1138, c33, c120, c182, c166, c174, c153, c53, c1191, c231, c110, c1192, c140, c40, c196, c32, c251, c31, c1189, c1144, c1163, c1125, c290] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1188 := derived1188 a h
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c1138 := derived1138 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c1191 := derived1191 a h
  have h14 : Entails.eval a c231 := h 230 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c1192 := derived1192 a h
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c40 := h 39 (by decide)
  have h19 : Entails.eval a c196 := h 195 (by decide)
  have h20 : Entails.eval a c32 := h 31 (by decide)
  have h21 : Entails.eval a c251 := h 250 (by decide)
  have h22 : Entails.eval a c31 := h 30 (by decide)
  have h23 : Entails.eval a c1189 := derived1189 a h
  have h24 : Entails.eval a c1144 := derived1144 a h
  have h25 : Entails.eval a c1163 := derived1163 a h
  have h26 : Entails.eval a c1125 := derived1125 a h
  have h27 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1194 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c140, some c40, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 57) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c8, c140, c40] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1195 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨13, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c166, some c1194, some c160, some c1090, some c109, some c231, some c110, some c1192, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 57) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c151, c1118, c372, c166, c1194, c160, c1090, c109, c231, c110, c1192] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c1194 := derived1194 a h
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c1090 := derived1090 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c1192 := derived1192 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c166, some c160, some c1090, some c108, some c209, some c253, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 57) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c151, c1118, c372, c166, c160, c1090, c108, c209, c253] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c1090 := derived1090 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c72, some c83, some c40, some c1158, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p1197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 57) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c372, c72, c83, c40, c1158] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c1158 := derived1158 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1198 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c1188, some c167, some c182, some c174, some c183, some c1138, some c33, some c120, some c1193, some c1195, some c1197, some c8, some c160, some c1196, some c116, some c420, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 57) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c151, c1118, c372, c1188, c167, c182, c174, c183, c1138, c33, c120, c1193, c1195, c1197, c8, c160, c1196, c116, c420] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1188 := derived1188 a h
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c174 := h 173 (by decide)
  have h7 : Entails.eval a c183 := h 182 (by decide)
  have h8 : Entails.eval a c1138 := derived1138 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c1193 := derived1193 a h
  have h12 : Entails.eval a c1195 := derived1195 a h
  have h13 : Entails.eval a c1197 := derived1197 a h
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c1196 := derived1196 a h
  have h17 : Entails.eval a c116 := h 115 (by decide)
  have h18 : Entails.eval a c420 := derived420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1199 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c1188, some c167, some c182, some c166, some c174, some c183, some c153, some c160, some c368, some c1090, some c109, some c108, some c250, some c173, some c378, some c377, some c361, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 57) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c151, c1118, c372, c1188, c167, c182, c166, c174, c183, c153, c160, c368, c1090, c109, c108, c250, c173, c378, c377, c361] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1188 := derived1188 a h
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c174 := h 173 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c1090 := derived1090 a h
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c378 := h 377 (by decide)
  have h18 : Entails.eval a c377 := h 376 (by decide)
  have h19 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨30, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1133, some c321, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 57) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c1133, c321] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c1133 := derived1133 a h
  have h1 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1201 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1199, some c151, some c1118, some c372, some c1188, some c167, some c1198, some c136, some c182, some c166, some c174, some c153, some c1138, some c8, some c72, some c83, some c40, some c374, some c378, some c303, some c65, some c86, some c410, some c315, some c100, some c1144, some c104, some c60, some c81, some c1200, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 57) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c1199, c151, c1118, c372, c1188, c167, c1198, c136, c182, c166, c174, c153, c1138, c8, c72, c83, c40, c374, c378, c303, c65, c86, c410, c315, c100, c1144, c104, c60, c81, c1200] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c1199 := derived1199 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c1188 := derived1188 a h
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c1198 := derived1198 a h
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c1138 := derived1138 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c40 := h 39 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c378 := h 377 (by decide)
  have h19 : Entails.eval a c303 := h 302 (by decide)
  have h20 : Entails.eval a c65 := h 64 (by decide)
  have h21 : Entails.eval a c86 := h 85 (by decide)
  have h22 : Entails.eval a c410 := derived410 a h
  have h23 : Entails.eval a c315 := h 314 (by decide)
  have h24 : Entails.eval a c100 := h 99 (by decide)
  have h25 : Entails.eval a c1144 := derived1144 a h
  have h26 : Entails.eval a c104 := h 103 (by decide)
  have h27 : Entails.eval a c60 := h 59 (by decide)
  have h28 : Entails.eval a c81 := h 80 (by decide)
  have h29 : Entails.eval a c1200 := derived1200 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c270, some c249, some c238, some c289, some c300, some c199, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 57) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c194, c270, c249, c238, c289, c300, c199] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c238 := h 237 (by decide)
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1203 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨33, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c66, some c374, some c330, some c329, some c368, some c361, some c1202, some c290, some c279, some c41, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 57) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c85, c66, c374, c330, c329, c368, c361, c1202, c290, c279, c41] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c330 := h 329 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c361 := h 360 (by decide)
  have h7 : Entails.eval a c1202 := derived1202 a h
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c279 := h 278 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1204 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c295, some c274, some c41, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 57) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c295, c274, c41] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c295 := h 294 (by decide)
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1205 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c372, some c1138, some c1188, some c167, some c153, some c182, some c174, some c166, some c1198, some c136, some c1199, some c1201, some c1203, some c378, some c377, some c72, some c361, some c368, some c73, some c315, some c314, some c1204, some c38, some c194, some c272, some c31, some c243, some c222, some c275, some c196, some c197, some c124, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 57) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c151, c1118, c372, c1138, c1188, c167, c153, c182, c174, c166, c1198, c136, c1199, c1201, c1203, c378, c377, c72, c361, c368, c73, c315, c314, c1204, c38, c194, c272, c31, c243, c222, c275, c196, c197, c124] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1138 := derived1138 a h
  have h4 : Entails.eval a c1188 := derived1188 a h
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c182 := h 181 (by decide)
  have h8 : Entails.eval a c174 := h 173 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c1198 := derived1198 a h
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c1199 := derived1199 a h
  have h13 : Entails.eval a c1201 := derived1201 a h
  have h14 : Entails.eval a c1203 := derived1203 a h
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c377 := h 376 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c361 := h 360 (by decide)
  have h19 : Entails.eval a c368 := h 367 (by decide)
  have h20 : Entails.eval a c73 := h 72 (by decide)
  have h21 : Entails.eval a c315 := h 314 (by decide)
  have h22 : Entails.eval a c314 := h 313 (by decide)
  have h23 : Entails.eval a c1204 := derived1204 a h
  have h24 : Entails.eval a c38 := h 37 (by decide)
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c272 := h 271 (by decide)
  have h27 : Entails.eval a c31 := h 30 (by decide)
  have h28 : Entails.eval a c243 := h 242 (by decide)
  have h29 : Entails.eval a c222 := h 221 (by decide)
  have h30 : Entails.eval a c275 := h 274 (by decide)
  have h31 : Entails.eval a c196 := h 195 (by decide)
  have h32 : Entails.eval a c197 := h 196 (by decide)
  have h33 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1206 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c330, some c329, some c194, some c270, some c243, some c238, some c289, some c992, some c105, some c197, some c106, some c122, some c229, some c199, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 57) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c330, c329, c194, c270, c243, c238, c289, c992, c105, c197, c106, c122, c229, c199] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c330 := h 329 (by decide)
  have h1 : Entails.eval a c329 := h 328 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c238 := h 237 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c992 := derived992 a h
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1207 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨30, by decide⟩, true), (⟨55, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c98, some c92, some c1125, some c100, some c103, some c976, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 57) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c99, c98, c92, c1125, c100, c103, c976] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c976 := derived976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1208 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c976, some c1164, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 57) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c976, c1164] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c976 := derived976 a h
  have h1 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1209 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1205, some c170, some c373, some c1118, some c151, some c374, some c377, some c156, some c72, some c361, some c1206, some c1207, some c33, some c1003, some c106, some c229, some c211, some c321, some c54, some c1208, some c8, some c21, some c105, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1209 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 57) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c1205, c170, c373, c1118, c151, c374, c377, c156, c72, c361, c1206, c1207, c33, c1003, c106, c229, c211, c321, c54, c1208, c8, c21, c105] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c1206 := derived1206 a h
  have h11 : Entails.eval a c1207 := derived1207 a h
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c1003 := derived1003 a h
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c229 := h 228 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c321 := h 320 (by decide)
  have h18 : Entails.eval a c54 := h 53 (by decide)
  have h19 : Entails.eval a c1208 := derived1208 a h
  have h20 : Entails.eval a c8 := h 7 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1210 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨30, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c156, some c72, some c15, some c931, some c38, some c70, some c90, some c325, some c1208, some c55, some c987, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p1210 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 57) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c156, c72, c15, c931, c38, c70, c90, c325, c1208, c55, c987] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c156 := h 155 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c1208 := derived1208 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c987 := derived987 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1211 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c33, some c55, some c289, some c321, some c54, some c104, some c83, some c50, some c102, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1211 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 57) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c33, c55, c289, c321, c54, c104, c83, c50, c102] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c289 := h 288 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1212 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨54, by decide⟩, true), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c987, some c92, some c1211, some c931, some c97, some c83, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p1212 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 57) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c373, c987, c92, c1211, c931, c97, c83] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c987 := derived987 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c931 := derived931 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1213 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c1118, some c151, some c59, some c35, some c147, some c283, some c111, some c208, some c231, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1213 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 57) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c194, c1118, c151, c59, c35, c147, c283, c111, c208, c231] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1214 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨52, by decide⟩, true), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, true), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1214 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c976, some c368, some c174, some c170, some c373, some c1118, some c372, some c931, some c97, some c96, some c92, some c13, some c103, some c176, some c992, some c240, some c18, some c237, some c194, some c206, some c1213, some c323, some c39, some c57, some c130, some c139, some c160, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1214 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1214 : lratChecker f1214 p1214 = .success := by decide +kernel
theorem unsat1214 : Unsatisfiable (PosFin 57) f1214 := by
  apply lratCheckerSound f1214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1214
  · intro a ha; simp [p1214] at ha; subst a; trivial
  · exact checked1214
theorem derived1214 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1214 := by
  apply localUnsat_implies_entails f1214 [c151, c976, c368, c174, c170, c373, c1118, c372, c931, c97, c96, c92, c13, c103, c176, c992, c240, c18, c237, c194, c206, c1213, c323, c39, c57, c130, c139, c160] c1214 unsat1214 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c976 := derived976 a h
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c931 := derived931 a h
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c992 := derived992 a h
  have h16 : Entails.eval a c240 := h 239 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c237 := h 236 (by decide)
  have h19 : Entails.eval a c194 := h 193 (by decide)
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c1213 := derived1213 a h
  have h22 : Entails.eval a c323 := h 322 (by decide)
  have h23 : Entails.eval a c39 := h 38 (by decide)
  have h24 : Entails.eval a c57 := h 56 (by decide)
  have h25 : Entails.eval a c130 := h 129 (by decide)
  have h26 : Entails.eval a c139 := h 138 (by decide)
  have h27 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1215 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1215 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1205, some c170, some c373, some c1209, some c174, some c1210, some c368, some c1118, some c372, some c1212, some c1214, some c33, some c53, some c73, some c1208, some c292, some c336, some c275, some c54, some c196, some c323, some c240, some c244, some c272, some c105, some c139, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1215 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1215 : lratChecker f1215 p1215 = .success := by decide +kernel
theorem unsat1215 : Unsatisfiable (PosFin 57) f1215 := by
  apply lratCheckerSound f1215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1215
  · intro a ha; simp [p1215] at ha; subst a; trivial
  · exact checked1215
theorem derived1215 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1215 := by
  apply localUnsat_implies_entails f1215 [c151, c1205, c170, c373, c1209, c174, c1210, c368, c1118, c372, c1212, c1214, c33, c53, c73, c1208, c292, c336, c275, c54, c196, c323, c240, c244, c272, c105, c139] c1215 unsat1215 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c1209 := derived1209 a h
  have h5 : Entails.eval a c174 := h 173 (by decide)
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c1118 := derived1118 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c1212 := derived1212 a h
  have h11 : Entails.eval a c1214 := derived1214 a h
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c1208 := derived1208 a h
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c275 := h 274 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c196 := h 195 (by decide)
  have h21 : Entails.eval a c323 := h 322 (by decide)
  have h22 : Entails.eval a c240 := h 239 (by decide)
  have h23 : Entails.eval a c244 := h 243 (by decide)
  have h24 : Entails.eval a c272 := h 271 (by decide)
  have h25 : Entails.eval a c105 := h 104 (by decide)
  have h26 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1216 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1216 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c170, some c33, some c292, some c174, some c151, some c90, some c54, some c321, some c55, some c101, some c13, some c53, some c992, some c336, some c240, some c196, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1216 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1216 : lratChecker f1216 p1216 = .success := by decide +kernel
theorem unsat1216 : Unsatisfiable (PosFin 57) f1216 := by
  apply lratCheckerSound f1216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1216
  · intro a ha; simp [p1216] at ha; subst a; trivial
  · exact checked1216
theorem derived1216 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1216 := by
  apply localUnsat_implies_entails f1216 [c170, c33, c292, c174, c151, c90, c54, c321, c55, c101, c13, c53, c992, c336, c240, c196] c1216 unsat1216 (by rfl) a
  have h0 : Entails.eval a c170 := h 169 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c992 := derived992 a h
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c240 := h 239 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1217 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1217 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1215, some c151, some c1205, some c170, some c373, some c1209, some c174, some c1210, some c1118, some c372, some c33, some c292, some c289, some c1216, some c1208, some c987, some c1053, some c55, some c1211, some c321, some c96, some c1159, some c102, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1217 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1217 : lratChecker f1217 p1217 = .success := by decide +kernel
theorem unsat1217 : Unsatisfiable (PosFin 57) f1217 := by
  apply lratCheckerSound f1217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1217
  · intro a ha; simp [p1217] at ha; subst a; trivial
  · exact checked1217
theorem derived1217 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1217 := by
  apply localUnsat_implies_entails f1217 [c1215, c151, c1205, c170, c373, c1209, c174, c1210, c1118, c372, c33, c292, c289, c1216, c1208, c987, c1053, c55, c1211, c321, c96, c1159, c102] c1217 unsat1217 (by rfl) a
  have h0 : Entails.eval a c1215 := derived1215 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c1209 := derived1209 a h
  have h6 : Entails.eval a c174 := h 173 (by decide)
  have h7 : Entails.eval a c1210 := derived1210 a h
  have h8 : Entails.eval a c1118 := derived1118 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c1216 := derived1216 a h
  have h14 : Entails.eval a c1208 := derived1208 a h
  have h15 : Entails.eval a c987 := derived987 a h
  have h16 : Entails.eval a c1053 := derived1053 a h
  have h17 : Entails.eval a c55 := h 54 (by decide)
  have h18 : Entails.eval a c1211 := derived1211 a h
  have h19 : Entails.eval a c321 := h 320 (by decide)
  have h20 : Entails.eval a c96 := h 95 (by decide)
  have h21 : Entails.eval a c1159 := derived1159 a h
  have h22 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1218 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨2, by decide⟩, false), (⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨3, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1218 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c281, some c294, some c191, some c190, some c21, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1218 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1218 : lratChecker f1218 p1218 = .success := by decide +kernel
theorem unsat1218 : Unsatisfiable (PosFin 57) f1218 := by
  apply lratCheckerSound f1218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1218
  · intro a ha; simp [p1218] at ha; subst a; trivial
  · exact checked1218
theorem derived1218 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1218 := by
  apply localUnsat_implies_entails f1218 [c281, c294, c191, c190, c21] c1218 unsat1218 (by rfl) a
  have h0 : Entails.eval a c281 := h 280 (by decide)
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1219 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨34, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1219 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1129, some c368, some c7, some c157, some c1218, some c48, some c283, some c275, some c262, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1219 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1219 : lratChecker f1219 p1219 = .success := by decide +kernel
theorem unsat1219 : Unsatisfiable (PosFin 57) f1219 := by
  apply lratCheckerSound f1219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1219
  · intro a ha; simp [p1219] at ha; subst a; trivial
  · exact checked1219
theorem derived1219 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1219 := by
  apply localUnsat_implies_entails f1219 [c1129, c368, c7, c157, c1218, c48, c283, c275, c262] c1219 unsat1219 (by rfl) a
  have h0 : Entails.eval a c1129 := derived1129 a h
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c1218 := derived1218 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1220 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1220 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c569, some c1219, some c34, some c296, some c294, some c49, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1220 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1220 : lratChecker f1220 p1220 = .success := by decide +kernel
theorem unsat1220 : Unsatisfiable (PosFin 57) f1220 := by
  apply lratCheckerSound f1220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1220
  · intro a ha; simp [p1220] at ha; subst a; trivial
  · exact checked1220
theorem derived1220 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1220 := by
  apply localUnsat_implies_entails f1220 [c103, c569, c1219, c34, c296, c294, c49] c1220 unsat1220 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c569 := derived569 a h
  have h2 : Entails.eval a c1219 := derived1219 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1221 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1221 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c240, some c18, some c237, some c1213, some c206, some c321, some c289, some c300, some c263, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1221 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1221 : lratChecker f1221 p1221 = .success := by decide +kernel
theorem unsat1221 : Unsatisfiable (PosFin 57) f1221 := by
  apply lratCheckerSound f1221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1221
  · intro a ha; simp [p1221] at ha; subst a; trivial
  · exact checked1221
theorem derived1221 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1221 := by
  apply localUnsat_implies_entails f1221 [c151, c240, c18, c237, c1213, c206, c321, c289, c300, c263] c1221 unsat1221 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c240 := h 239 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c1213 := derived1213 a h
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c321 := h 320 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1222 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1222 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1209, some c174, some c1205, some c170, some c373, some c151, some c1118, some c372, some c1210, some c1215, some c1217, some c931, some c83, some c97, some c96, some c1220, some c1221, some c992, some c189, some c13, some c292, some c1128, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1222 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1222 : lratChecker f1222 p1222 = .success := by decide +kernel
theorem unsat1222 : Unsatisfiable (PosFin 57) f1222 := by
  apply lratCheckerSound f1222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1222
  · intro a ha; simp [p1222] at ha; subst a; trivial
  · exact checked1222
theorem derived1222 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1222 := by
  apply localUnsat_implies_entails f1222 [c1209, c174, c1205, c170, c373, c151, c1118, c372, c1210, c1215, c1217, c931, c83, c97, c96, c1220, c1221, c992, c189, c13, c292, c1128] c1222 unsat1222 (by rfl) a
  have h0 : Entails.eval a c1209 := derived1209 a h
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c1210 := derived1210 a h
  have h9 : Entails.eval a c1215 := derived1215 a h
  have h10 : Entails.eval a c1217 := derived1217 a h
  have h11 : Entails.eval a c931 := derived931 a h
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c1220 := derived1220 a h
  have h16 : Entails.eval a c1221 := derived1221 a h
  have h17 : Entails.eval a c992 := derived992 a h
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c13 := h 12 (by decide)
  have h20 : Entails.eval a c292 := h 291 (by decide)
  have h21 : Entails.eval a c1128 := derived1128 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1223 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1223 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c109, some c242, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p1223 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1223 : lratChecker f1223 p1223 = .success := by decide +kernel
theorem unsat1223 : Unsatisfiable (PosFin 57) f1223 := by
  apply lratCheckerSound f1223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1223
  · intro a ha; simp [p1223] at ha; subst a; trivial
  · exact checked1223
theorem derived1223 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1223 := by
  apply localUnsat_implies_entails f1223 [c112, c109, c242] c1223 unsat1223 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1224 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1224 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c81, some c101, some c13, some c159, some c165, some c186, some c1068, some c223, some c1223, some c1074, some c18, some c33, some c53, some c292, some c336, some c40, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1224 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1224 : lratChecker f1224 p1224 = .success := by decide +kernel
theorem unsat1224 : Unsatisfiable (PosFin 57) f1224 := by
  apply lratCheckerSound f1224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1224
  · intro a ha; simp [p1224] at ha; subst a; trivial
  · exact checked1224
theorem derived1224 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1224 := by
  apply localUnsat_implies_entails f1224 [c81, c101, c13, c159, c165, c186, c1068, c223, c1223, c1074, c18, c33, c53, c292, c336, c40] c1224 unsat1224 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c159 := h 158 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c1068 := derived1068 a h
  have h7 : Entails.eval a c223 := h 222 (by decide)
  have h8 : Entails.eval a c1223 := derived1223 a h
  have h9 : Entails.eval a c1074 := derived1074 a h
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1225 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1225 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c931, some c102, some c15, some c53, some c165, some c334, some c13, some c55, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1225 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1225 : lratChecker f1225 p1225 = .success := by decide +kernel
theorem unsat1225 : Unsatisfiable (PosFin 57) f1225 := by
  apply lratCheckerSound f1225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1225
  · intro a ha; simp [p1225] at ha; subst a; trivial
  · exact checked1225
theorem derived1225 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1225 := by
  apply localUnsat_implies_entails f1225 [c1224, c931, c102, c15, c53, c165, c334, c13, c55] c1225 unsat1225 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1226 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨44, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1226 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c68, some c13, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1226 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1226 : lratChecker f1226 p1226 = .success := by decide +kernel
theorem unsat1226 : Unsatisfiable (PosFin 57) f1226 := by
  apply lratCheckerSound f1226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1226
  · intro a ha; simp [p1226] at ha; subst a; trivial
  · exact checked1226
theorem derived1226 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1226 := by
  apply localUnsat_implies_entails f1226 [c152, c68, c13] c1226 unsat1226 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1227 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1227 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1225, some c156, some c72, some c15, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p1227 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1227 : lratChecker f1227 p1227 = .success := by decide +kernel
theorem unsat1227 : Unsatisfiable (PosFin 57) f1227 := by
  apply lratCheckerSound f1227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1227
  · intro a ha; simp [p1227] at ha; subst a; trivial
  · exact checked1227
theorem derived1227 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1227 := by
  apply localUnsat_implies_entails f1227 [c1225, c156, c72, c15] c1227 unsat1227 (by rfl) a
  have h0 : Entails.eval a c1225 := derived1225 a h
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1228 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1228 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1227, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1228 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1228 : lratChecker f1228 p1228 = .success := by decide +kernel
theorem unsat1228 : Unsatisfiable (PosFin 57) f1228 := by
  apply lratCheckerSound f1228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1228
  · intro a ha; simp [p1228] at ha; subst a; trivial
  · exact checked1228
theorem derived1228 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1228 := by
  apply localUnsat_implies_entails f1228 [c1226, c1227] c1228 unsat1228 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1227 := derived1227 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1229 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1229 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1209, some c174, some c1205, some c170, some c373, some c151, some c1118, some c372, some c1222, some c1228, some c90, some c96, some c104, some c83, some c50, some c931, some c289, some c33, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1229 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1229 : lratChecker f1229 p1229 = .success := by decide +kernel
theorem unsat1229 : Unsatisfiable (PosFin 57) f1229 := by
  apply lratCheckerSound f1229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1229
  · intro a ha; simp [p1229] at ha; subst a; trivial
  · exact checked1229
theorem derived1229 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1229 := by
  apply localUnsat_implies_entails f1229 [c1209, c174, c1205, c170, c373, c151, c1118, c372, c1222, c1228, c90, c96, c104, c83, c50, c931, c289, c33] c1229 unsat1229 (by rfl) a
  have h0 : Entails.eval a c1209 := derived1209 a h
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c1222 := derived1222 a h
  have h9 : Entails.eval a c1228 := derived1228 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c931 := derived931 a h
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1230 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, true), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1230 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c75, some c185, some c100, some c157, some c56, some c319, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1230 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1230 : lratChecker f1230 p1230 = .success := by decide +kernel
theorem unsat1230 : Unsatisfiable (PosFin 57) f1230 := by
  apply lratCheckerSound f1230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1230
  · intro a ha; simp [p1230] at ha; subst a; trivial
  · exact checked1230
theorem derived1230 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1230 := by
  apply localUnsat_implies_entails f1230 [c159, c75, c185, c100, c157, c56, c319] c1230 unsat1230 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1231 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨33, by decide⟩, false), (⟨54, by decide⟩, true), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1231 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1205, some c170, some c329, some c174, some c373, some c151, some c1118, some c372, some c38, some c70, some c90, some c96, some c314, some c104, some c83, some c931, some c1230, some c368, some c976, some c157, some c987, some c8, some c185, some c1053, some c156, some c1060, some c176, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1231 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1231 : lratChecker f1231 p1231 = .success := by decide +kernel
theorem unsat1231 : Unsatisfiable (PosFin 57) f1231 := by
  apply lratCheckerSound f1231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1231
  · intro a ha; simp [p1231] at ha; subst a; trivial
  · exact checked1231
theorem derived1231 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1231 := by
  apply localUnsat_implies_entails f1231 [c1205, c170, c329, c174, c373, c151, c1118, c372, c38, c70, c90, c96, c314, c104, c83, c931, c1230, c368, c976, c157, c987, c8, c185, c1053, c156, c1060, c176] c1231 unsat1231 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c314 := h 313 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c931 := derived931 a h
  have h16 : Entails.eval a c1230 := derived1230 a h
  have h17 : Entails.eval a c368 := h 367 (by decide)
  have h18 : Entails.eval a c976 := derived976 a h
  have h19 : Entails.eval a c157 := h 156 (by decide)
  have h20 : Entails.eval a c987 := derived987 a h
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c185 := h 184 (by decide)
  have h23 : Entails.eval a c1053 := derived1053 a h
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c1060 := derived1060 a h
  have h26 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1232 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨33, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1232 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c931, some c102, some c976, some c73, some c104, some c103, some c315, some c60, some c92, some c57, some c334, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1232 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1232 : lratChecker f1232 p1232 = .success := by decide +kernel
theorem unsat1232 : Unsatisfiable (PosFin 57) f1232 := by
  apply lratCheckerSound f1232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1232
  · intro a ha; simp [p1232] at ha; subst a; trivial
  · exact checked1232
theorem derived1232 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1232 := by
  apply localUnsat_implies_entails f1232 [c368, c931, c102, c976, c73, c104, c103, c315, c60, c92, c57, c334] c1232 unsat1232 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c976 := derived976 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1233 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨33, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1233 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c1232, some c72, some c83, some c332, some c104, some c103, some c40, some c92, some c569, some c1129, some c296, some c34, some c190, some c571, some c21, some c215, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1233 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1233 : lratChecker f1233 p1233 = .success := by decide +kernel
theorem unsat1233 : Unsatisfiable (PosFin 57) f1233 := by
  apply lratCheckerSound f1233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1233
  · intro a ha; simp [p1233] at ha; subst a; trivial
  · exact checked1233
theorem derived1233 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1233 := by
  apply localUnsat_implies_entails f1233 [c372, c1232, c72, c83, c332, c104, c103, c40, c92, c569, c1129, c296, c34, c190, c571, c21, c215] c1233 unsat1233 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c1232 := derived1232 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c569 := derived569 a h
  have h10 : Entails.eval a c1129 := derived1129 a h
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c571 := derived571 a h
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1234 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨44, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1234 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c1205, some c170, some c373, some c1209, some c1229, some c1231, some c1233, some c329, some c174, some c72, some c332, some c59, some c40, some c321, some c292, some c296, some c61, some c101, some c13, some c41, some c992, some c1214, some c240, some c645, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1234 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1234 : lratChecker f1234 p1234 = .success := by decide +kernel
theorem unsat1234 : Unsatisfiable (PosFin 57) f1234 := by
  apply lratCheckerSound f1234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1234
  · intro a ha; simp [p1234] at ha; subst a; trivial
  · exact checked1234
theorem derived1234 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1234 := by
  apply localUnsat_implies_entails f1234 [c151, c1118, c1205, c170, c373, c1209, c1229, c1231, c1233, c329, c174, c72, c332, c59, c40, c321, c292, c296, c61, c101, c13, c41, c992, c1214, c240, c645] c1234 unsat1234 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c1209 := derived1209 a h
  have h6 : Entails.eval a c1229 := derived1229 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c1233 := derived1233 a h
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c321 := h 320 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c296 := h 295 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c101 := h 100 (by decide)
  have h20 : Entails.eval a c13 := h 12 (by decide)
  have h21 : Entails.eval a c41 := h 40 (by decide)
  have h22 : Entails.eval a c992 := derived992 a h
  have h23 : Entails.eval a c1214 := derived1214 a h
  have h24 : Entails.eval a c240 := h 239 (by decide)
  have h25 : Entails.eval a c645 := derived645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1235 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1235 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1209, some c1229, some c1231, some c1205, some c170, some c373, some c1118, some c151, some c368, some c1233, some c1234, some c931, some c102, some c73, some c1181, some c231, some c223, some c106, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1235 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1235 : lratChecker f1235 p1235 = .success := by decide +kernel
theorem unsat1235 : Unsatisfiable (PosFin 57) f1235 := by
  apply lratCheckerSound f1235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1235
  · intro a ha; simp [p1235] at ha; subst a; trivial
  · exact checked1235
theorem derived1235 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1235 := by
  apply localUnsat_implies_entails f1235 [c1209, c1229, c1231, c1205, c170, c373, c1118, c151, c368, c1233, c1234, c931, c102, c73, c1181, c231, c223, c106] c1235 unsat1235 (by rfl) a
  have h0 : Entails.eval a c1209 := derived1209 a h
  have h1 : Entails.eval a c1229 := derived1229 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c151 := h 150 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c1233 := derived1233 a h
  have h10 : Entails.eval a c1234 := derived1234 a h
  have h11 : Entails.eval a c931 := derived931 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c1181 := derived1181 a h
  have h15 : Entails.eval a c231 := h 230 (by decide)
  have h16 : Entails.eval a c223 := h 222 (by decide)
  have h17 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1236 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨44, by decide⟩, true), (⟨6, by decide⟩, false), (⟨33, by decide⟩, false), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1236 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c329, some c373, some c931, some c102, some c15, some c156, some c165, some c332, some c13, some c1171, some c292, some c289, some c271, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1236 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1236 : lratChecker f1236 p1236 = .success := by decide +kernel
theorem unsat1236 : Unsatisfiable (PosFin 57) f1236 := by
  apply lratCheckerSound f1236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1236
  · intro a ha; simp [p1236] at ha; subst a; trivial
  · exact checked1236
theorem derived1236 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1236 := by
  apply localUnsat_implies_entails f1236 [c1226, c329, c373, c931, c102, c15, c156, c165, c332, c13, c1171, c292, c289, c271] c1236 unsat1236 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c329 := h 328 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c332 := h 331 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c1171 := derived1171 a h
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1237 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1237 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1205, some c170, some c1209, some c174, some c1229, some c329, some c1231, some c1235, some c1236, some c72, some c81, some c332, some c101, some c13, some c40, some c165, some c292, some c296, some c186, some c41, some c1068, some c18, some c240, some c237, some c1069, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1237 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1237 : lratChecker f1237 p1237 = .success := by decide +kernel
theorem unsat1237 : Unsatisfiable (PosFin 57) f1237 := by
  apply lratCheckerSound f1237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1237
  · intro a ha; simp [p1237] at ha; subst a; trivial
  · exact checked1237
theorem derived1237 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1237 := by
  apply localUnsat_implies_entails f1237 [c1205, c170, c1209, c174, c1229, c329, c1231, c1235, c1236, c72, c81, c332, c101, c13, c40, c165, c292, c296, c186, c41, c1068, c18, c240, c237, c1069] c1237 unsat1237 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c1209 := derived1209 a h
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c1229 := derived1229 a h
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c1231 := derived1231 a h
  have h7 : Entails.eval a c1235 := derived1235 a h
  have h8 : Entails.eval a c1236 := derived1236 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c332 := h 331 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c296 := h 295 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c41 := h 40 (by decide)
  have h20 : Entails.eval a c1068 := derived1068 a h
  have h21 : Entails.eval a c18 := h 17 (by decide)
  have h22 : Entails.eval a c240 := h 239 (by decide)
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1238 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨33, by decide⟩, false), (⟨44, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1238 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1237, some c1205, some c170, some c174, some c1236, some c72, some c81, some c332, some c13, some c40, some c165, some c131, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1238 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1238 : lratChecker f1238 p1238 = .success := by decide +kernel
theorem unsat1238 : Unsatisfiable (PosFin 57) f1238 := by
  apply lratCheckerSound f1238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1238
  · intro a ha; simp [p1238] at ha; subst a; trivial
  · exact checked1238
theorem derived1238 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1238 := by
  apply localUnsat_implies_entails f1238 [c1237, c1205, c170, c174, c1236, c72, c81, c332, c13, c40, c165, c131] c1238 unsat1238 (by rfl) a
  have h0 : Entails.eval a c1237 := derived1237 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c1236 := derived1236 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1239 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1239 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c377, some c361, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1239 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1239 : lratChecker f1239 p1239 = .success := by decide +kernel
theorem unsat1239 : Unsatisfiable (PosFin 57) f1239 := by
  apply lratCheckerSound f1239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1239
  · intro a ha; simp [p1239] at ha; subst a; trivial
  · exact checked1239
theorem derived1239 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1239 := by
  apply localUnsat_implies_entails f1239 [c374, c377, c361] c1239 unsat1239 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1240 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1240 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1205, some c170, some c373, some c1118, some c1239, some c174, some c1238, some c1228, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1240 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1240 : lratChecker f1240 p1240 = .success := by decide +kernel
theorem unsat1240 : Unsatisfiable (PosFin 57) f1240 := by
  apply lratCheckerSound f1240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1240
  · intro a ha; simp [p1240] at ha; subst a; trivial
  · exact checked1240
theorem derived1240 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1240 := by
  apply localUnsat_implies_entails f1240 [c1205, c170, c373, c1118, c1239, c174, c1238, c1228] c1240 unsat1240 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c1239 := derived1239 a h
  have h5 : Entails.eval a c174 := h 173 (by decide)
  have h6 : Entails.eval a c1238 := derived1238 a h
  have h7 : Entails.eval a c1228 := derived1228 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1241 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1241 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c156, some c72, some c15, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1241 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1241 : lratChecker f1241 p1241 = .success := by decide +kernel
theorem unsat1241 : Unsatisfiable (PosFin 57) f1241 := by
  apply lratCheckerSound f1241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1241
  · intro a ha; simp [p1241] at ha; subst a; trivial
  · exact checked1241
theorem derived1241 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1241 := by
  apply localUnsat_implies_entails f1241 [c156, c72, c15] c1241 unsat1241 (by rfl) a
  have h0 : Entails.eval a c156 := h 155 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1242 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨14, by decide⟩, false), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1242 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c1220, some c92, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p1242 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1242 : lratChecker f1242 p1242 = .success := by decide +kernel
theorem unsat1242 : Unsatisfiable (PosFin 57) f1242 := by
  apply lratCheckerSound f1242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1242
  · intro a ha; simp [p1242] at ha; subst a; trivial
  · exact checked1242
theorem derived1242 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1242 := by
  apply localUnsat_implies_entails f1242 [c103, c1220, c92] c1242 unsat1242 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c1220 := derived1220 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1243 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1243 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c111, some c229, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1243 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1243 : lratChecker f1243 p1243 = .success := by decide +kernel
theorem unsat1243 : Unsatisfiable (PosFin 57) f1243 := by
  apply lratCheckerSound f1243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1243
  · intro a ha; simp [p1243] at ha; subst a; trivial
  · exact checked1243
theorem derived1243 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1243 := by
  apply localUnsat_implies_entails f1243 [c113, c111, c229] c1243 unsat1243 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1244 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨14, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1244 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c368, some c170, some c1118, some c92, some c13, some c992, some c176, some c240, some c18, some c1243, some c186, some c1074, some c157, some c223, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1244 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1244 : lratChecker f1244 p1244 = .success := by decide +kernel
theorem unsat1244 : Unsatisfiable (PosFin 57) f1244 := by
  apply lratCheckerSound f1244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1244
  · intro a ha; simp [p1244] at ha; subst a; trivial
  · exact checked1244
theorem derived1244 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1244 := by
  apply localUnsat_implies_entails f1244 [c151, c368, c170, c1118, c92, c13, c992, c176, c240, c18, c1243, c186, c1074, c157, c223] c1244 unsat1244 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c992 := derived992 a h
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c240 := h 239 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c1243 := derived1243 a h
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c1074 := derived1074 a h
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1245 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1245 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c368, some c160, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1245 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1245 : lratChecker f1245 p1245 = .success := by decide +kernel
theorem unsat1245 : Unsatisfiable (PosFin 57) f1245 := by
  apply lratCheckerSound f1245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1245
  · intro a ha; simp [p1245] at ha; subst a; trivial
  · exact checked1245
theorem derived1245 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1245 := by
  apply localUnsat_implies_entails f1245 [c371, c368, c160] c1245 unsat1245 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1246 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1246 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c80, some c81, some c372, some c166, some c160, some c370, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1246 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1246 : lratChecker f1246 p1246 = .success := by decide +kernel
theorem unsat1246 : Unsatisfiable (PosFin 57) f1246 := by
  apply lratCheckerSound f1246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1246
  · intro a ha; simp [p1246] at ha; subst a; trivial
  · exact checked1246
theorem derived1246 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1246 := by
  apply localUnsat_implies_entails f1246 [c1245, c80, c81, c372, c166, c160, c370] c1246 unsat1246 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1247 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1247 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c287, some c49, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1247 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1247 : lratChecker f1247 p1247 = .success := by decide +kernel
theorem unsat1247 : Unsatisfiable (PosFin 57) f1247 := by
  apply lratCheckerSound f1247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1247
  · intro a ha; simp [p1247] at ha; subst a; trivial
  · exact checked1247
theorem derived1247 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1247 := by
  apply localUnsat_implies_entails f1247 [c285, c287, c49] c1247 unsat1247 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1248 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1248 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c377, some c93, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1248 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1248 : lratChecker f1248 p1248 = .success := by decide +kernel
theorem unsat1248 : Unsatisfiable (PosFin 57) f1248 := by
  apply lratCheckerSound f1248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1248
  · intro a ha; simp [p1248] at ha; subst a; trivial
  · exact checked1248
theorem derived1248 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1248 := by
  apply localUnsat_implies_entails f1248 [c378, c377, c93] c1248 unsat1248 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1249 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1249 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c150, some c1248, some c154, some c285, some c1247, some c48, some c49, some c36, some c72, some c296, some c324, some c841, some c92, some c569, some c1117, some c286, some c264, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1249 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1249 : lratChecker f1249 p1249 = .success := by decide +kernel
theorem unsat1249 : Unsatisfiable (PosFin 57) f1249 := by
  apply lratCheckerSound f1249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1249
  · intro a ha; simp [p1249] at ha; subst a; trivial
  · exact checked1249
theorem derived1249 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1249 := by
  apply localUnsat_implies_entails f1249 [c160, c150, c1248, c154, c285, c1247, c48, c49, c36, c72, c296, c324, c841, c92, c569, c1117, c286, c264] c1249 unsat1249 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c1248 := derived1248 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c1247 := derived1247 a h
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c296 := h 295 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c569 := derived569 a h
  have h15 : Entails.eval a c1117 := derived1117 a h
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1250 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1250 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c49, some c36, some c288, some c280, some c324, some c318, some c71, some c264, some c302, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1250 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1250 : lratChecker f1250 p1250 = .success := by decide +kernel
theorem unsat1250 : Unsatisfiable (PosFin 57) f1250 := by
  apply lratCheckerSound f1250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1250
  · intro a ha; simp [p1250] at ha; subst a; trivial
  · exact checked1250
theorem derived1250 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1250 := by
  apply localUnsat_implies_entails f1250 [c48, c49, c36, c288, c280, c324, c318, c71, c264, c302] c1250 unsat1250 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1251 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1251 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c93, some c841, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1251 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1251 : lratChecker f1251 p1251 = .success := by decide +kernel
theorem unsat1251 : Unsatisfiable (PosFin 57) f1251 := by
  apply lratCheckerSound f1251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1251
  · intro a ha; simp [p1251] at ha; subst a; trivial
  · exact checked1251
theorem derived1251 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1251 := by
  apply localUnsat_implies_entails f1251 [c92, c93, c841] c1251 unsat1251 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1252 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1252 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1249, some c369, some c154, some c166, some c1248, some c172, some c301, some c49, some c1250, some c303, some c72, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1252 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1252 : lratChecker f1252 p1252 = .success := by decide +kernel
theorem unsat1252 : Unsatisfiable (PosFin 57) f1252 := by
  apply lratCheckerSound f1252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1252
  · intro a ha; simp [p1252] at ha; subst a; trivial
  · exact checked1252
theorem derived1252 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1252 := by
  apply localUnsat_implies_entails f1252 [c1251, c1249, c369, c154, c166, c1248, c172, c301, c49, c1250, c303, c72] c1252 unsat1252 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1249 := derived1249 a h
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c1248 := derived1248 a h
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c1250 := derived1250 a h
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1253 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1253 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c81, some c80, some c48, some c49, some c288, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1253 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1253 : lratChecker f1253 p1253 = .success := by decide +kernel
theorem unsat1253 : Unsatisfiable (PosFin 57) f1253 := by
  apply lratCheckerSound f1253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1253
  · intro a ha; simp [p1253] at ha; subst a; trivial
  · exact checked1253
theorem derived1253 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1253 := by
  apply localUnsat_implies_entails f1253 [c81, c80, c48, c49, c288] c1253 unsat1253 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1254 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1254 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1252, some c80, some c81, some c1253, some c301, some c309, some c178, some c154, some c300, some c370, some c287, some c150, some c40, some c328, some c60, some c334, some c340, some c264, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1254 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1254 : lratChecker f1254 p1254 = .success := by decide +kernel
theorem unsat1254 : Unsatisfiable (PosFin 57) f1254 := by
  apply lratCheckerSound f1254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1254
  · intro a ha; simp [p1254] at ha; subst a; trivial
  · exact checked1254
theorem derived1254 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1254 := by
  apply localUnsat_implies_entails f1254 [c1251, c1252, c80, c81, c1253, c301, c309, c178, c154, c300, c370, c287, c150, c40, c328, c60, c334, c340, c264] c1254 unsat1254 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1252 := derived1252 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c1253 := derived1253 a h
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c300 := h 299 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c340 := h 339 (by decide)
  have h18 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1255 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨26, by decide⟩, true), (⟨29, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1255 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c261, some c313, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p1255 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1255 : lratChecker f1255 p1255 = .success := by decide +kernel
theorem unsat1255 : Unsatisfiable (PosFin 57) f1255 := by
  apply lratCheckerSound f1255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1255
  · intro a ha; simp [p1255] at ha; subst a; trivial
  · exact checked1255
theorem derived1255 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1255 := by
  apply localUnsat_implies_entails f1255 [c264, c261, c313] c1255 unsat1255 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1256 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1256 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c318, some c61, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1256 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1256 : lratChecker f1256 p1256 = .success := by decide +kernel
theorem unsat1256 : Unsatisfiable (PosFin 57) f1256 := by
  apply lratCheckerSound f1256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1256
  · intro a ha; simp [p1256] at ha; subst a; trivial
  · exact checked1256
theorem derived1256 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1256 := by
  apply localUnsat_implies_entails f1256 [c320, c318, c61] c1256 unsat1256 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1257 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1257 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c154, some c166, some c1248, some c150, some c172, some c1250, some c300, some c278, some c1256, some c264, some c324, some c61, some c60, some c342, some c71, some c328, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1257 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1257 : lratChecker f1257 p1257 = .success := by decide +kernel
theorem unsat1257 : Unsatisfiable (PosFin 57) f1257 := by
  apply lratCheckerSound f1257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1257
  · intro a ha; simp [p1257] at ha; subst a; trivial
  · exact checked1257
theorem derived1257 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1257 := by
  apply localUnsat_implies_entails f1257 [c1251, c154, c166, c1248, c150, c172, c1250, c300, c278, c1256, c264, c324, c61, c60, c342, c71, c328] c1257 unsat1257 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c1248 := derived1248 a h
  have h4 : Entails.eval a c150 := h 149 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c1250 := derived1250 a h
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c1256 := derived1256 a h
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1258 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨29, by decide⟩, true), (⟨47, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨30, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1258 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c326, some c61, some c270, some c325, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1258 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1258 : lratChecker f1258 p1258 = .success := by decide +kernel
theorem unsat1258 : Unsatisfiable (PosFin 57) f1258 := by
  apply lratCheckerSound f1258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1258
  · intro a ha; simp [p1258] at ha; subst a; trivial
  · exact checked1258
theorem derived1258 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1258 := by
  apply localUnsat_implies_entails f1258 [c328, c326, c61, c270, c325] c1258 unsat1258 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c326 := h 325 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1259 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨15, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1259 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1258, some c39, some c60, some c127, some c325, some c836, some c266, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1259 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1259 : lratChecker f1259 p1259 = .success := by decide +kernel
theorem unsat1259 : Unsatisfiable (PosFin 57) f1259 := by
  apply lratCheckerSound f1259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1259
  · intro a ha; simp [p1259] at ha; subst a; trivial
  · exact checked1259
theorem derived1259 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1259 := by
  apply localUnsat_implies_entails f1259 [c1251, c1258, c39, c60, c127, c325, c836, c266] c1259 unsat1259 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1258 := derived1258 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  have h6 : Entails.eval a c836 := derived836 a h
  have h7 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1260 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨47, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1260 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1259, some c286, some c284, some c48, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1260 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1260 : lratChecker f1260 p1260 = .success := by decide +kernel
theorem unsat1260 : Unsatisfiable (PosFin 57) f1260 := by
  apply lratCheckerSound f1260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1260
  · intro a ha; simp [p1260] at ha; subst a; trivial
  · exact checked1260
theorem derived1260 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1260 := by
  apply localUnsat_implies_entails f1260 [c1259, c286, c284, c48] c1260 unsat1260 (by rfl) a
  have h0 : Entails.eval a c1259 := derived1259 a h
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1261 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨30, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1261 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1246, some c1251, some c1257, some c370, some c366, some c160, some c150, some c1248, some c376, some c178, some c354, some c373, some c71, some c180, some c1260, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1261 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1261 : lratChecker f1261 p1261 = .success := by decide +kernel
theorem unsat1261 : Unsatisfiable (PosFin 57) f1261 := by
  apply lratCheckerSound f1261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1261
  · intro a ha; simp [p1261] at ha; subst a; trivial
  · exact checked1261
theorem derived1261 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1261 := by
  apply localUnsat_implies_entails f1261 [c1246, c1251, c1257, c370, c366, c160, c150, c1248, c376, c178, c354, c373, c71, c180, c1260] c1261 unsat1261 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c1257 := derived1257 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c1248 := derived1248 a h
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c373 := h 372 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c1260 := derived1260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1262 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨56, by decide⟩, false), (⟨43, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1262 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c166, some c1248, some c374, some c365, some c172, some c354, some c379, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1262 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1262 : lratChecker f1262 p1262 = .success := by decide +kernel
theorem unsat1262 : Unsatisfiable (PosFin 57) f1262 := by
  apply lratCheckerSound f1262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1262
  · intro a ha; simp [p1262] at ha; subst a; trivial
  · exact checked1262
theorem derived1262 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1262 := by
  apply localUnsat_implies_entails f1262 [c154, c166, c1248, c374, c365, c172, c354, c379] c1262 unsat1262 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c1248 := derived1248 a h
  have h3 : Entails.eval a c374 := h 373 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1263 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1263 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c569, some c294, some c576, some c571, some c190, some c113, some c23, some c21, some c125, some c202, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1263 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1263 : lratChecker f1263 p1263 = .success := by decide +kernel
theorem unsat1263 : Unsatisfiable (PosFin 57) f1263 := by
  apply lratCheckerSound f1263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1263
  · intro a ha; simp [p1263] at ha; subst a; trivial
  · exact checked1263
theorem derived1263 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1263 := by
  apply localUnsat_implies_entails f1263 [c100, c569, c294, c576, c571, c190, c113, c23, c21, c125, c202] c1263 unsat1263 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c569 := derived569 a h
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c576 := derived576 a h
  have h4 : Entails.eval a c571 := derived571 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1264 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1264 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c98, some c2, some c5, some c1254, some c1246, some c1251, some c1261, some c72, some c1117, some c841, some c1262, some c369, some c160, some c150, some c1248, some c569, some c180, some c183, some c1263, some c48, some c49, some c36, some c286, some c296, some c324, some c264, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1264 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1264 : lratChecker f1264 p1264 = .success := by decide +kernel
theorem unsat1264 : Unsatisfiable (PosFin 57) f1264 := by
  apply lratCheckerSound f1264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1264
  · intro a ha; simp [p1264] at ha; subst a; trivial
  · exact checked1264
theorem derived1264 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1264 := by
  apply localUnsat_implies_entails f1264 [c100, c98, c2, c5, c1254, c1246, c1251, c1261, c72, c1117, c841, c1262, c369, c160, c150, c1248, c569, c180, c183, c1263, c48, c49, c36, c286, c296, c324, c264] c1264 unsat1264 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c1246 := derived1246 a h
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c1261 := derived1261 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1117 := derived1117 a h
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c1262 := derived1262 a h
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c1248 := derived1248 a h
  have h16 : Entails.eval a c569 := derived569 a h
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c183 := h 182 (by decide)
  have h19 : Entails.eval a c1263 := derived1263 a h
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c49 := h 48 (by decide)
  have h22 : Entails.eval a c36 := h 35 (by decide)
  have h23 : Entails.eval a c286 := h 285 (by decide)
  have h24 : Entails.eval a c296 := h 295 (by decide)
  have h25 : Entails.eval a c324 := h 323 (by decide)
  have h26 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1265 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨30, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1265 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c341, some c340, some c270, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1265 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1265 : lratChecker f1265 p1265 = .success := by decide +kernel
theorem unsat1265 : Unsatisfiable (PosFin 57) f1265 := by
  apply lratCheckerSound f1265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1265
  · intro a ha; simp [p1265] at ha; subst a; trivial
  · exact checked1265
theorem derived1265 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1265 := by
  apply localUnsat_implies_entails f1265 [c341, c340, c270] c1265 unsat1265 (by rfl) a
  have h0 : Entails.eval a c341 := h 340 (by decide)
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1266 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1266 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c81, some c80, some c61, some c60, some c328, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1266 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1266 : lratChecker f1266 p1266 = .success := by decide +kernel
theorem unsat1266 : Unsatisfiable (PosFin 57) f1266 := by
  apply lratCheckerSound f1266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1266
  · intro a ha; simp [p1266] at ha; subst a; trivial
  · exact checked1266
theorem derived1266 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1266 := by
  apply localUnsat_implies_entails f1266 [c81, c80, c61, c60, c328] c1266 unsat1266 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1267 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1267 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1248, some c172, some c300, some c1265, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1267 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1267 : lratChecker f1267 p1267 = .success := by decide +kernel
theorem unsat1267 : Unsatisfiable (PosFin 57) f1267 := by
  apply lratCheckerSound f1267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1267
  · intro a ha; simp [p1267] at ha; subst a; trivial
  · exact checked1267
theorem derived1267 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1267 := by
  apply localUnsat_implies_entails f1267 [c1248, c172, c300, c1265] c1267 unsat1267 (by rfl) a
  have h0 : Entails.eval a c1248 := derived1248 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c1265 := derived1265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1268 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1268 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c100, some c98, some c1251, some c5, some c1254, some c1264, some c81, some c1253, some c1266, some c1267, some c178, some c154, some c300, some c340, some c370, some c270, some c150, some c349, some c294, some c264, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1268 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1268 : lratChecker f1268 p1268 = .success := by decide +kernel
theorem unsat1268 : Unsatisfiable (PosFin 57) f1268 := by
  apply lratCheckerSound f1268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1268
  · intro a ha; simp [p1268] at ha; subst a; trivial
  · exact checked1268
theorem derived1268 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1268 := by
  apply localUnsat_implies_entails f1268 [c2, c100, c98, c1251, c5, c1254, c1264, c81, c1253, c1266, c1267, c178, c154, c300, c340, c370, c270, c150, c349, c294, c264] c1268 unsat1268 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1251 := derived1251 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1254 := derived1254 a h
  have h6 : Entails.eval a c1264 := derived1264 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c1253 := derived1253 a h
  have h9 : Entails.eval a c1266 := derived1266 a h
  have h10 : Entails.eval a c1267 := derived1267 a h
  have h11 : Entails.eval a c178 := h 177 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c300 := h 299 (by decide)
  have h14 : Entails.eval a c340 := h 339 (by decide)
  have h15 : Entails.eval a c370 := h 369 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c150 := h 149 (by decide)
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c294 := h 293 (by decide)
  have h20 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1269 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1269 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c166, some c162, some c371, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1269 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1269 : lratChecker f1269 p1269 = .success := by decide +kernel
theorem unsat1269 : Unsatisfiable (PosFin 57) f1269 := by
  apply lratCheckerSound f1269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1269
  · intro a ha; simp [p1269] at ha; subst a; trivial
  · exact checked1269
theorem derived1269 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1269 := by
  apply localUnsat_implies_entails f1269 [c166, c162, c371] c1269 unsat1269 (by rfl) a
  have h0 : Entails.eval a c166 := h 165 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1270 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨28, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1270 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1247, some c1251, some c379, some c300, some c151, some c1118, some c1265, some c281, some c1129, some c61, some c266, some c327, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1270 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1270 : lratChecker f1270 p1270 = .success := by decide +kernel
theorem unsat1270 : Unsatisfiable (PosFin 57) f1270 := by
  apply lratCheckerSound f1270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1270
  · intro a ha; simp [p1270] at ha; subst a; trivial
  · exact checked1270
theorem derived1270 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1270 := by
  apply localUnsat_implies_entails f1270 [c1247, c1251, c379, c300, c151, c1118, c1265, c281, c1129, c61, c266, c327] c1270 unsat1270 (by rfl) a
  have h0 : Entails.eval a c1247 := derived1247 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c1265 := derived1265 a h
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c1129 := derived1129 a h
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1271 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨29, by decide⟩, true), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false), (⟨30, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1271 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c341, some c270, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1271 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1271 : lratChecker f1271 p1271 = .success := by decide +kernel
theorem unsat1271 : Unsatisfiable (PosFin 57) f1271 := by
  apply lratCheckerSound f1271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1271
  · intro a ha; simp [p1271] at ha; subst a; trivial
  · exact checked1271
theorem derived1271 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1271 := by
  apply localUnsat_implies_entails f1271 [c324, c341, c270] c1271 unsat1271 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1272 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1272 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1247, some c1251, some c1270, some c153, some c371, some c284, some c151, some c297, some c1271, some c61, some c60, some c327, some c270, some c266, some c352, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1272 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1272 : lratChecker f1272 p1272 = .success := by decide +kernel
theorem unsat1272 : Unsatisfiable (PosFin 57) f1272 := by
  apply lratCheckerSound f1272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1272
  · intro a ha; simp [p1272] at ha; subst a; trivial
  · exact checked1272
theorem derived1272 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1272 := by
  apply localUnsat_implies_entails f1272 [c1247, c1251, c1270, c153, c371, c284, c151, c297, c1271, c61, c60, c327, c270, c266, c352] c1272 unsat1272 (by rfl) a
  have h0 : Entails.eval a c1247 := derived1247 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c1270 := derived1270 a h
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c1271 := derived1271 a h
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1273 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1273 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1247, some c1251, some c1272, some c48, some c49, some c36, some c288, some c341, some c1118, some c71, some c337, some c299, some c266, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1273 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1273 : lratChecker f1273 p1273 = .success := by decide +kernel
theorem unsat1273 : Unsatisfiable (PosFin 57) f1273 := by
  apply lratCheckerSound f1273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1273
  · intro a ha; simp [p1273] at ha; subst a; trivial
  · exact checked1273
theorem derived1273 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1273 := by
  apply localUnsat_implies_entails f1273 [c1247, c1251, c1272, c48, c49, c36, c288, c341, c1118, c71, c337, c299, c266] c1273 unsat1273 (by rfl) a
  have h0 : Entails.eval a c1247 := derived1247 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c1272 := derived1272 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c1118 := derived1118 a h
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c337 := h 336 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1274 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1274 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c174, some c178, some c379, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1274 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1274 : lratChecker f1274 p1274 = .success := by decide +kernel
theorem unsat1274 : Unsatisfiable (PosFin 57) f1274 := by
  apply lratCheckerSound f1274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1274
  · intro a ha; simp [p1274] at ha; subst a; trivial
  · exact checked1274
theorem derived1274 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1274 := by
  apply localUnsat_implies_entails f1274 [c174, c178, c379] c1274 unsat1274 (by rfl) a
  have h0 : Entails.eval a c174 := h 173 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1275 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1275 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1274, some c1248, some c1269, some c369, some c1273, some c1205, some c72, some c1117, some c379, some c374, some c153, some c353, some c365, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1275 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1275 : lratChecker f1275 p1275 = .success := by decide +kernel
theorem unsat1275 : Unsatisfiable (PosFin 57) f1275 := by
  apply lratCheckerSound f1275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1275
  · intro a ha; simp [p1275] at ha; subst a; trivial
  · exact checked1275
theorem derived1275 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1275 := by
  apply localUnsat_implies_entails f1275 [c1251, c1274, c1248, c1269, c369, c1273, c1205, c72, c1117, c379, c374, c153, c353, c365] c1275 unsat1275 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1274 := derived1274 a h
  have h2 : Entails.eval a c1248 := derived1248 a h
  have h3 : Entails.eval a c1269 := derived1269 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c1273 := derived1273 a h
  have h6 : Entails.eval a c1205 := derived1205 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c1117 := derived1117 a h
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1276 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1276 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c166, some c162, some c372, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1276 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1276 : lratChecker f1276 p1276 = .success := by decide +kernel
theorem unsat1276 : Unsatisfiable (PosFin 57) f1276 := by
  apply lratCheckerSound f1276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1276
  · intro a ha; simp [p1276] at ha; subst a; trivial
  · exact checked1276
theorem derived1276 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1276 := by
  apply localUnsat_implies_entails f1276 [c166, c162, c372] c1276 unsat1276 (by rfl) a
  have h0 : Entails.eval a c166 := h 165 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1277 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1277 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c300, some c1265, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1277 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1277 : lratChecker f1277 p1277 = .success := by decide +kernel
theorem unsat1277 : Unsatisfiable (PosFin 57) f1277 := by
  apply lratCheckerSound f1277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1277
  · intro a ha; simp [p1277] at ha; subst a; trivial
  · exact checked1277
theorem derived1277 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1277 := by
  apply localUnsat_implies_entails f1277 [c301, c300, c1265] c1277 unsat1277 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c300 := h 299 (by decide)
  have h2 : Entails.eval a c1265 := derived1265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1278 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1278 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c97, some c98, some c1251, some c2, some c1, some c1268, some c1274, some c1275, some c80, some c1253, some c1266, some c301, some c341, some c1277, some c153, some c372, some c151, some c297, some c337, some c266, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1278 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1278 : lratChecker f1278 p1278 = .success := by decide +kernel
theorem unsat1278 : Unsatisfiable (PosFin 57) f1278 := by
  apply lratCheckerSound f1278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1278
  · intro a ha; simp [p1278] at ha; subst a; trivial
  · exact checked1278
theorem derived1278 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1278 := by
  apply localUnsat_implies_entails f1278 [c100, c97, c98, c1251, c2, c1, c1268, c1274, c1275, c80, c1253, c1266, c301, c341, c1277, c153, c372, c151, c297, c337, c266] c1278 unsat1278 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1251 := derived1251 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1268 := derived1268 a h
  have h7 : Entails.eval a c1274 := derived1274 a h
  have h8 : Entails.eval a c1275 := derived1275 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c1253 := derived1253 a h
  have h11 : Entails.eval a c1266 := derived1266 a h
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c1277 := derived1277 a h
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c151 := h 150 (by decide)
  have h18 : Entails.eval a c297 := h 296 (by decide)
  have h19 : Entails.eval a c337 := h 336 (by decide)
  have h20 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1279 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1279 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c157, some c160, some c365, some c366, some c71, some c72, some c841, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1279 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1279 : lratChecker f1279 p1279 = .success := by decide +kernel
theorem unsat1279 : Unsatisfiable (PosFin 57) f1279 := by
  apply lratCheckerSound f1279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1279
  · intro a ha; simp [p1279] at ha; subst a; trivial
  · exact checked1279
theorem derived1279 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1279 := by
  apply localUnsat_implies_entails f1279 [c369, c157, c160, c365, c366, c71, c72, c841] c1279 unsat1279 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c365 := h 364 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1280 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1280 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c60, some c328, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1280 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1280 : lratChecker f1280 p1280 = .success := by decide +kernel
theorem unsat1280 : Unsatisfiable (PosFin 57) f1280 := by
  apply lratCheckerSound f1280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1280
  · intro a ha; simp [p1280] at ha; subst a; trivial
  · exact checked1280
theorem derived1280 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1280 := by
  apply localUnsat_implies_entails f1280 [c61, c60, c328] c1280 unsat1280 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived1280

end CochromaticTwenty.Certificates.B16_8_2
