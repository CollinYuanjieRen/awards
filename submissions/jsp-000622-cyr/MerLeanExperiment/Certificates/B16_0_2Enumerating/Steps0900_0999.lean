import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps0800_0899

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1314 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c105, some c108, some c1294, some c1305, some c1308, some c203, some c1309, some c198, some c8, some c1313, some c266, some c1292, some c819, some c810, some c140, some c1225, some c50, some c236, some c210, some c134, some c47, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 57) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c110, c105, c108, c1294, c1305, c1308, c203, c1309, c198, c8, c1313, c266, c1292, c819, c810, c140, c1225, c50, c236, c210, c134, c47] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c1305 := derived1305 a h
  have h5 : Entails.eval a c1308 := derived1308 a h
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c1309 := derived1309 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c1313 := derived1313 a h
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c1292 := derived1292 a h
  have h13 : Entails.eval a c819 := derived819 a h
  have h14 : Entails.eval a c810 := derived810 a h
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c1225 := derived1225 a h
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c236 := h 235 (by decide)
  have h19 : Entails.eval a c210 := h 209 (by decide)
  have h20 : Entails.eval a c134 := h 133 (by decide)
  have h21 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1296, some c261, some c490, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 57) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c1296, c261, c490] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c1296 := derived1296 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c490 := derived490 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c50, some c142, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 57) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c41, c50, c142] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c110, some c1147, some c1299, some c1314, some c105, some c1301, some c1316, some c208, some c1296, some c122, some c262, some c261, some c8, some c28, some c7, some c27, some c168, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 57) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c108, c110, c1147, c1299, c1314, c105, c1301, c1316, c208, c1296, c122, c262, c261, c8, c28, c7, c27, c168] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c1314 := derived1314 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1301 := derived1301 a h
  have h7 : Entails.eval a c1316 := derived1316 a h
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c1296 := derived1296 a h
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c262 := h 261 (by decide)
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c7 := h 6 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  have h17 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c137, some c42, some c77, some c133, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 57) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c150, c137, c42, c77, c133] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1314, some c110, some c105, some c108, some c1275, some c1147, some c1317, some c200, some c4, some c16, some c204, some c1318, some c41, some c113, some c133, some c77, some c178, some c853, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c1314, c110, c105, c108, c1275, c1147, c1317, c200, c4, c16, c204, c1318, c41, c113, c133, c77, c178, c853] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c1314 := derived1314 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c1147 := derived1147 a h
  have h6 : Entails.eval a c1317 := derived1317 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c1318 := derived1318 a h
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c77 := h 76 (by decide)
  have h16 : Entails.eval a c178 := h 177 (by decide)
  have h17 : Entails.eval a c853 := derived853 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c778, some c115, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c45, c778, c115] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c778 := derived778 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c108, some c819, some c7, some c1320, some c114, some c1292, some c1299, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c110, c108, c819, c7, c1320, c114, c1292, c1299] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c819 := derived819 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1320 := derived1320 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c1292 := derived1292 a h
  have h7 : Entails.eval a c1299 := derived1299 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c121, some c47, some c45, some c115, some c135, some c1296, some c81, some c86, some c214, some c169, some c294, some c230, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c114, c121, c47, c45, c115, c135, c1296, c81, c86, c214, c169, c294, c230] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c1296 := derived1296 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c214 := h 213 (by decide)
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c294 := h 293 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1314, some c1316, some c1319, some c134, some c141, some c83, some c81, some c42, some c294, some c170, some c77, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1314, c1316, c1319, c134, c141, c83, c81, c42, c294, c170, c77] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1314 := derived1314 a h
  have h1 : Entails.eval a c1316 := derived1316 a h
  have h2 : Entails.eval a c1319 := derived1319 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1319, some c1314, some c110, some c108, some c1316, some c1322, some c1299, some c1323, some c47, some c45, some c214, some c210, some c1296, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1319, c1314, c110, c108, c1316, c1322, c1299, c1323, c47, c45, c214, c210, c1296] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1319 := derived1319 a h
  have h1 : Entails.eval a c1314 := derived1314 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1316 := derived1316 a h
  have h5 : Entails.eval a c1322 := derived1322 a h
  have h6 : Entails.eval a c1299 := derived1299 a h
  have h7 : Entails.eval a c1323 := derived1323 a h
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c1296 := derived1296 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c114, some c141, some c1299, some c41, some c1292, some c144, some c819, some c204, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c110, c114, c141, c1299, c41, c1292, c144, c819, c204] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c1292 := derived1292 a h
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c591, some c261, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c7, c591, c261] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c28, some c1326, some c204, some c168, some c124, some c27, some c261, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c8, c28, c1326, c204, c168, c124, c27, c261] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c1326 := derived1326 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c1327, some c753, some c262, some c204, some c210, some c1296, some c124, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c121, c1327, c753, c262, c204, c210, c1296, c124] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c1327 := derived1327 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c1296 := derived1296 a h
  have h7 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c108, some c110, some c1314, some c1319, some c1324, some c1325, some c47, some c45, some c1328, some c1299, some c1292, some c210, some c819, some c264, some c204, some c36, some c1216, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c105, c108, c110, c1314, c1319, c1324, c1325, c47, c45, c1328, c1299, c1292, c210, c819, c264, c204, c36, c1216] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1314 := derived1314 a h
  have h4 : Entails.eval a c1319 := derived1319 a h
  have h5 : Entails.eval a c1324 := derived1324 a h
  have h6 : Entails.eval a c1325 := derived1325 a h
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c1328 := derived1328 a h
  have h10 : Entails.eval a c1299 := derived1299 a h
  have h11 : Entails.eval a c1292 := derived1292 a h
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c819 := derived819 a h
  have h14 : Entails.eval a c264 := h 263 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c197, some c41, some c1004, some c150, some c313, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c197, c41, c1004, c150, c313] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c197 := h 196 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c1004 := derived1004 a h
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1329, some c105, some c108, some c1275, some c1147, some c20, some c1299, some c199, some c8, some c262, some c1330, some c205, some c45, some c146, some c147, some c317, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c1329, c105, c108, c1275, c1147, c20, c1299, c199, c8, c262, c1330, c205, c45, c146, c147, c317] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c1329 := derived1329 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c1299 := derived1299 a h
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c1330 := derived1330 a h
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c16, some c201, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c20, c16, c201] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c41, some c1004, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c44, c41, c1004] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c1004 := derived1004 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c885, some c127, some c1296, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c199, c885, c127, c1296] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c885 := derived885 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c1296 := derived1296 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c263, some c40, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c262, c263, c40] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c45, some c147, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c48, c45, c147] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1329, some c1332, some c1331, some c199, some c1333, some c1334, some c1335, some c1336, some c205, some c266, some c1261, some c40, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c108, c105, c1329, c1332, c1331, c199, c1333, c1334, c1335, c1336, c205, c266, c1261, c40] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1331 := derived1331 a h
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c1333 := derived1333 a h
  have h7 : Entails.eval a c1334 := derived1334 a h
  have h8 : Entails.eval a c1335 := derived1335 a h
  have h9 : Entails.eval a c1336 := derived1336 a h
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c1261 := derived1261 a h
  have h13 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1296, some c122, some c262, some c261, some c8, some c28, some c27, some c168, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c1296, c122, c262, c261, c8, c28, c27, c168] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c1296 := derived1296 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c72, some c76, some c158, some c270, some c217, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c72, c76, c158, c270, c217] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c72 := h 71 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1332, some c1339, some c168, some c166, some c73, some c220, some c158, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1332, c1339, c168, c166, c73, c220, c158] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1332 := derived1332 a h
  have h1 : Entails.eval a c1339 := derived1339 a h
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1332, some c1275, some c1147, some c1338, some c208, some c117, some c45, some c115, some c146, some c135, some c142, some c317, some c316, some c147, some c215, some c1335, some c1340, some c4, some c136, some c237, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c108, c1332, c1275, c1147, c1338, c208, c117, c45, c115, c146, c135, c142, c317, c316, c147, c215, c1335, c1340, c4, c136, c237] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1275 := derived1275 a h
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c1338 := derived1338 a h
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c142 := h 141 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c215 := h 214 (by decide)
  have h16 : Entails.eval a c1335 := derived1335 a h
  have h17 : Entails.eval a c1340 := derived1340 a h
  have h18 : Entails.eval a c4 := h 3 (by decide)
  have h19 : Entails.eval a c136 := h 135 (by decide)
  have h20 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c1296, some c122, some c115, some c1335, some c261, some c127, some c27, some c209, some c889, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c208, c1296, c122, c115, c1335, c261, c127, c27, c209, c889] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c1296 := derived1296 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c1335 := derived1335 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c889 := derived889 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1332, some c1339, some c166, some c220, some c1083, some c158, some c275, some c60, some c62, some c257, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c1332, c1339, c166, c220, c1083, c158, c275, c60, c62, c257] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c1332 := derived1332 a h
  have h1 : Entails.eval a c1339 := derived1339 a h
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c220 := h 219 (by decide)
  have h4 : Entails.eval a c1083 := derived1083 a h
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c275 := h 274 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1332, some c1341, some c1342, some c48, some c45, some c1336, some c115, some c135, some c142, some c202, some c1296, some c1147, some c146, some c117, some c215, some c316, some c1335, some c1343, some c4, some c136, some c237, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c108, c1332, c1341, c1342, c48, c45, c1336, c115, c135, c142, c202, c1296, c1147, c146, c117, c215, c316, c1335, c1343, c4, c136, c237] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1341 := derived1341 a h
  have h3 : Entails.eval a c1342 := derived1342 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c1296 := derived1296 a h
  have h12 : Entails.eval a c1147 := derived1147 a h
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c215 := h 214 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  have h17 : Entails.eval a c1335 := derived1335 a h
  have h18 : Entails.eval a c1343 := derived1343 a h
  have h19 : Entails.eval a c4 := h 3 (by decide)
  have h20 : Entails.eval a c136 := h 135 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1316, some c113, some c122, some c264, some c1296, some c4, some c201, some c1147, some c1299, some c266, some c44, some c215, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c1316, c113, c122, c264, c1296, c4, c201, c1147, c1299, c266, c44, c215] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c1316 := derived1316 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c1296 := derived1296 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c1299 := derived1299 a h
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1275, some c1299, some c1147, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c1275, c1299, c1147] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c1275 := derived1275 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1329, some c1337, some c1316, some c1344, some c1346, some c1345, some c1335, some c265, some c36, some c896, some c261, some c215, some c44, some c133, some c230, some c77, some c174, some c288, some c81, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c108, c105, c1329, c1337, c1316, c1344, c1346, c1345, c1335, c265, c36, c896, c261, c215, c44, c133, c230, c77, c174, c288, c81] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c1337 := derived1337 a h
  have h4 : Entails.eval a c1316 := derived1316 a h
  have h5 : Entails.eval a c1344 := derived1344 a h
  have h6 : Entails.eval a c1346 := derived1346 a h
  have h7 : Entails.eval a c1345 := derived1345 a h
  have h8 : Entails.eval a c1335 := derived1335 a h
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c896 := derived896 a h
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c215 := h 214 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c77 := h 76 (by decide)
  have h18 : Entails.eval a c174 := h 173 (by decide)
  have h19 : Entails.eval a c288 := h 287 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c202, some c896, some c127, some c264, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c202, c896, c127, c264] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c202 := h 201 (by decide)
  have h1 : Entails.eval a c896 := derived896 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1329, some c105, some c108, some c1337, some c1316, some c1344, some c1345, some c1335, some c1346, some c1348, some c1147, some c265, some c1347, some c36, some c48, some c261, some c215, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c1329, c105, c108, c1337, c1316, c1344, c1345, c1335, c1346, c1348, c1147, c265, c1347, c36, c48, c261, c215] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c1329 := derived1329 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1337 := derived1337 a h
  have h4 : Entails.eval a c1316 := derived1316 a h
  have h5 : Entails.eval a c1344 := derived1344 a h
  have h6 : Entails.eval a c1345 := derived1345 a h
  have h7 : Entails.eval a c1335 := derived1335 a h
  have h8 : Entails.eval a c1346 := derived1346 a h
  have h9 : Entails.eval a c1348 := derived1348 a h
  have h10 : Entails.eval a c1147 := derived1147 a h
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c1347 := derived1347 a h
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c45, some c115, some c1296, some c124, some c197, some c7, some c1320, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c114, c45, c115, c1296, c124, c197, c7, c1320] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1296 := derived1296 a h
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c1320 := derived1320 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1350, some c108, some c134, some c81, some c135, some c50, some c144, some c197, some c20, some c7, some c198, some c175, some c84, some c1268, some c1299, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1350, c108, c134, c81, c135, c50, c144, c197, c20, c7, c198, c175, c84, c1268, c1299] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1350 := derived1350 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c198 := h 197 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c1268 := derived1268 a h
  have h14 : Entails.eval a c1299 := derived1299 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1350, some c1351, some c45, some c115, some c135, some c264, some c81, some c86, some c36, some c172, some c1320, some c197, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c108, c1350, c1351, c45, c115, c135, c264, c81, c86, c36, c172, c1320, c197] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1350 := derived1350 a h
  have h2 : Entails.eval a c1351 := derived1351 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c1320 := derived1320 a h
  have h12 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1352, some c114, some c121, some c45, some c1335, some c115, some c135, some c142, some c1296, some c81, some c124, some c215, some c169, some c317, some c917, some c314, some c230, some c880, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1352, c114, c121, c45, c1335, c115, c135, c142, c1296, c81, c124, c215, c169, c317, c917, c314, c230, c880] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1352 := derived1352 a h
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c1335 := derived1335 a h
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  have h8 : Entails.eval a c1296 := derived1296 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c917 := derived917 a h
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c880 := derived880 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨45, by decide⟩, true), (⟨25, by decide⟩, false), (⟨42, by decide⟩, false), (⟨29, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c44, some c295, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c84, c44, c295] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c1147, some c26, some c1229, some c264, some c122, some c1335, some c8, some c28, some c167, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 57) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c1299, c1147, c26, c1229, c264, c122, c1335, c8, c28, c167] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c1229 := derived1229 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c1335 := derived1335 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1329, some c1349, some c1352, some c1316, some c1353, some c1355, some c134, some c141, some c81, some c1354, some c170, some c77, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 57) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c108, c105, c1329, c1349, c1352, c1316, c1353, c1355, c134, c141, c81, c1354, c170, c77] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c1349 := derived1349 a h
  have h4 : Entails.eval a c1352 := derived1352 a h
  have h5 : Entails.eval a c1316 := derived1316 a h
  have h6 : Entails.eval a c1353 := derived1353 a h
  have h7 : Entails.eval a c1355 := derived1355 a h
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c1354 := derived1354 a h
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1329, some c105, some c108, some c1349, some c1352, some c1316, some c1353, some c1355, some c1356, some c45, some c48, some c135, some c81, some c86, some c169, some c295, some c80, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 57) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c1329, c105, c108, c1349, c1352, c1316, c1353, c1355, c1356, c45, c48, c135, c81, c86, c169, c295, c80] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c1329 := derived1329 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1349 := derived1349 a h
  have h4 : Entails.eval a c1352 := derived1352 a h
  have h5 : Entails.eval a c1316 := derived1316 a h
  have h6 : Entails.eval a c1353 := derived1353 a h
  have h7 : Entails.eval a c1355 := derived1355 a h
  have h8 : Entails.eval a c1356 := derived1356 a h
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c48 := h 47 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c205, some c1335, some c885, some c120, some c1296, some c261, some c27, some c209, some c163, some c284, some c223, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 57) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c199, c205, c1335, c885, c120, c1296, c261, c27, c209, c163, c284, c223] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c1335 := derived1335 a h
  have h3 : Entails.eval a c885 := derived885 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c1296 := derived1296 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1329, some c1332, some c1357, some c200, some c1294, some c1333, some c199, some c4, some c204, some c45, some c48, some c448, some c140, some c120, some c286, some c1335, some c86, some c206, some c1296, some c1225, some c237, some c243, some c178, some c1217, some c62, some c257, some c182, some c356, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 57) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c108, c105, c1329, c1332, c1357, c200, c1294, c1333, c199, c4, c204, c45, c48, c448, c140, c120, c286, c1335, c86, c206, c1296, c1225, c237, c243, c178, c1217, c62, c257, c182, c356] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c1294 := derived1294 a h
  have h7 : Entails.eval a c1333 := derived1333 a h
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c448 := derived448 a h
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c1335 := derived1335 a h
  have h18 : Entails.eval a c86 := h 85 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c1296 := derived1296 a h
  have h21 : Entails.eval a c1225 := derived1225 a h
  have h22 : Entails.eval a c237 := h 236 (by decide)
  have h23 : Entails.eval a c243 := h 242 (by decide)
  have h24 : Entails.eval a c178 := h 177 (by decide)
  have h25 : Entails.eval a c1217 := derived1217 a h
  have h26 : Entails.eval a c62 := h 61 (by decide)
  have h27 : Entails.eval a c257 := h 256 (by decide)
  have h28 : Entails.eval a c182 := h 181 (by decide)
  have h29 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1357, some c200, some c4, some c105, some c1329, some c1332, some c1294, some c1333, some c1359, some c1358, some c265, some c1261, some c40, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 57) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c108, c1357, c200, c4, c105, c1329, c1332, c1294, c1333, c1359, c1358, c265, c1261, c40] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c1329 := derived1329 a h
  have h6 : Entails.eval a c1332 := derived1332 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c1333 := derived1333 a h
  have h9 : Entails.eval a c1359 := derived1359 a h
  have h10 : Entails.eval a c1358 := derived1358 a h
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c1261 := derived1261 a h
  have h13 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c137, some c77, some c240, some c171, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 57) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c117, c137, c77, c240, c171] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c77 := h 76 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨45, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c178, some c853, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 57) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c1147, c178, c853] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c853 := derived853 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1329, some c105, some c108, some c1332, some c200, some c204, some c4, some c1360, some c1361, some c41, some c113, some c133, some c77, some c1362, some c1275, some c202, some c80, some c179, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 57) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1357, c1329, c105, c108, c1332, c200, c204, c4, c1360, c1361, c41, c113, c133, c77, c1362, c1275, c202, c80, c179] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1329 := derived1329 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c1360 := derived1360 a h
  have h9 : Entails.eval a c1361 := derived1361 a h
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c1362 := derived1362 a h
  have h15 : Entails.eval a c1275 := derived1275 a h
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c80 := h 79 (by decide)
  have h18 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c819, some c7, some c261, some c206, some c41, some c314, some c578, some c139, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 57) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c105, c819, c7, c261, c206, c41, c314, c578, c139] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c819 := derived819 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c206 := h 205 (by decide)
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c578 := derived578 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c105, some c1294, some c203, some c124, some c1296, some c1364, some c199, some c8, some c1335, some c206, some c41, some c1330, some c1004, some c1312, some c154, some c155, some c76, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 57) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c114, c105, c1294, c203, c124, c1296, c1364, c199, c8, c1335, c206, c41, c1330, c1004, c1312, c154, c155, c76] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c1296 := derived1296 a h
  have h6 : Entails.eval a c1364 := derived1364 a h
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c1335 := derived1335 a h
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c1330 := derived1330 a h
  have h13 : Entails.eval a c1004 := derived1004 a h
  have h14 : Entails.eval a c1312 := derived1312 a h
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1363, some c1357, some c1329, some c105, some c108, some c114, some c45, some c1365, some c48, some c819, some c204, some c199, some c1333, some c124, some c120, some c1296, some c1335, some c206, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 57) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c1363, c1357, c1329, c105, c108, c114, c45, c1365, c48, c819, c204, c199, c1333, c124, c120, c1296, c1335, c206] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c1363 := derived1363 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c1365 := derived1365 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c819 := derived819 a h
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c1333 := derived1333 a h
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c1296 := derived1296 a h
  have h16 : Entails.eval a c1335 := derived1335 a h
  have h17 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c40, some c1268, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 57) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c1299, c40, c1268] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c1268 := derived1268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨26, by decide⟩, true), (⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c20, some c819, some c16, some c198, some c44, some c203, some c179, some c144, some c77, some c50, some c286, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 57) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c105, c20, c819, c16, c198, c44, c203, c179, c144, c77, c50, c286] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c819 := derived819 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1368, some c204, some c199, some c1333, some c144, some c179, some c50, some c77, some c286, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 57) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c1368, c204, c199, c1333, c144, c179, c50, c77, c286] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c1368 := derived1368 a h
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c1333 := derived1333 a h
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1329, some c1363, some c1366, some c1367, some c1357, some c134, some c81, some c84, some c1369, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 57) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c108, c105, c1329, c1363, c1366, c1367, c1357, c134, c81, c84, c1369] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c1363 := derived1363 a h
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c1367 := derived1367 a h
  have h6 : Entails.eval a c1357 := derived1357 a h
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c1369 := derived1369 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1363, some c1329, some c105, some c108, some c1366, some c1367, some c1370, some c48, some c819, some c199, some c120, some c266, some c40, some c1263, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 57) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c1363, c1329, c105, c108, c1366, c1367, c1370, c48, c819, c199, c120, c266, c40, c1263] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c1363 := derived1363 a h
  have h1 : Entails.eval a c1329 := derived1329 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c1367 := derived1367 a h
  have h6 : Entails.eval a c1370 := derived1370 a h
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c819 := derived819 a h
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c1263 := derived1263 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c1327, some c1335, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 57) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c121, c1327, c1335] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c1327 := derived1327 a h
  have h2 : Entails.eval a c1335 := derived1335 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c203, some c16, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 57) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c204, c203, c16] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1373, some c1372, some c1299, some c1147, some c40, some c26, some c1229, some c264, some c1216, some c819, some c604, some c73, some c72, some c283, some c284, some c1266, some c145, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 57) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c108, c1373, c1372, c1299, c1147, c40, c26, c1229, c264, c1216, c819, c604, c73, c72, c283, c284, c1266, c145] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1373 := derived1373 a h
  have h2 : Entails.eval a c1372 := derived1372 a h
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c1229 := derived1229 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c1216 := derived1216 a h
  have h10 : Entails.eval a c819 := derived819 a h
  have h11 : Entails.eval a c604 := derived604 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c1266 := derived1266 a h
  have h17 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c121, some c124, some c45, some c48, some c1335, some c1296, some c211, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 57) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c114, c121, c124, c45, c48, c1335, c1296, c211] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c1335 := derived1335 a h
  have h6 : Entails.eval a c1296 := derived1296 a h
  have h7 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c141, some c144, some c41, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 57) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c141, c144, c41] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c137, some c1296, some c77, some c86, some c169, some c1175, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 57) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c117, c137, c1296, c77, c86, c169, c1175] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c1296 := derived1296 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c1175 := derived1175 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1329, some c1357, some c1363, some c1371, some c1373, some c1374, some c1375, some c1376, some c45, some c48, some c1377, some c41, some c133, some c77, some c80, some c172, some c291, some c81, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 57) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c108, c105, c1329, c1357, c1363, c1371, c1373, c1374, c1375, c1376, c45, c48, c1377, c41, c133, c77, c80, c172, c291, c81] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c1357 := derived1357 a h
  have h4 : Entails.eval a c1363 := derived1363 a h
  have h5 : Entails.eval a c1371 := derived1371 a h
  have h6 : Entails.eval a c1373 := derived1373 a h
  have h7 : Entails.eval a c1374 := derived1374 a h
  have h8 : Entails.eval a c1375 := derived1375 a h
  have h9 : Entails.eval a c1376 := derived1376 a h
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c1377 := derived1377 a h
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c77 := h 76 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c291 := h 290 (by decide)
  have h19 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c42, some c146, some c152, some c319, some c208, some c268, some c261, some c1303, some c153, some c271, some c61, some c63, some c258, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 57) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c7, c42, c146, c152, c319, c208, c268, c261, c1303, c153, c271, c61, c63, c258] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c1303 := derived1303 a h
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c261, some c39, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 57) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c262, c261, c39] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1378, some c108, some c110, some c1275, some c1294, some c1346, some c1137, some c1147, some c1301, some c7, some c1380, some c205, some c42, some c1379, some c146, some c150, some c152, some c319, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 57) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c1378, c108, c110, c1275, c1294, c1346, c1137, c1147, c1301, c7, c1380, c205, c42, c1379, c146, c150, c152, c319] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c1378 := derived1378 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1294 := derived1294 a h
  have h5 : Entails.eval a c1346 := derived1346 a h
  have h6 : Entails.eval a c1137 := derived1137 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c1301 := derived1301 a h
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c1380 := derived1380 a h
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c1379 := derived1379 a h
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c150 := h 149 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c1004, some c149, some c318, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 57) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c199, c1004, c149, c318] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c1004 := derived1004 a h
  have h2 : Entails.eval a c149 := h 148 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1378, some c108, some c1381, some c1332, some c1137, some c197, some c199, some c18, some c5, some c1336, some c201, some c4, some c267, some c115, some c127, some c1335, some c1382, some c44, some c205, some c265, some c40, some c1216, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 57) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1378, c108, c1381, c1332, c1137, c197, c199, c18, c5, c1336, c201, c4, c267, c115, c127, c1335, c1382, c44, c205, c265, c40, c1216] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1378 := derived1378 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1381 := derived1381 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1137 := derived1137 a h
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c1336 := derived1336 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c1335 := derived1335 a h
  have h16 : Entails.eval a c1382 := derived1382 a h
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  have h20 : Entails.eval a c40 := h 39 (by decide)
  have h21 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨8, by decide⟩, false), (⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c44, some c1004, some c140, some c120, some c312, some c84, some c209, some c289, some c244, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 57) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c199, c44, c1004, c140, c120, c312, c84, c209, c289, c244] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c1004 := derived1004 a h
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨15, by decide⟩, false), (⟨21, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c199, some c1384, some c205, some c1335, some c261, some c120, some c27, some c209, some c163, some c284, some c223, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 57) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c106, c199, c1384, c205, c1335, c261, c120, c27, c209, c163, c284, c223] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c1384 := derived1384 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c1335 := derived1335 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c1216, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 57) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c40, c1216] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1387 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1378, some c108, some c1383, some c1373, some c200, some c5, some c4, some c16, some c1294, some c267, some c199, some c106, some c1386, some c265, some c1385, some c45, some c48, some c1004, some c140, some c120, some c149, some c243, some c1335, some c316, some c206, some c312, some c296, some c244, some c27, some c163, some c155, some c218, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 57) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c1378, c108, c1383, c1373, c200, c5, c4, c16, c1294, c267, c199, c106, c1386, c265, c1385, c45, c48, c1004, c140, c120, c149, c243, c1335, c316, c206, c312, c296, c244, c27, c163, c155, c218] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c1378 := derived1378 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c1373 := derived1373 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c1294 := derived1294 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c1386 := derived1386 a h
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c1385 := derived1385 a h
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c48 := h 47 (by decide)
  have h17 : Entails.eval a c1004 := derived1004 a h
  have h18 : Entails.eval a c140 := h 139 (by decide)
  have h19 : Entails.eval a c120 := h 119 (by decide)
  have h20 : Entails.eval a c149 := h 148 (by decide)
  have h21 : Entails.eval a c243 := h 242 (by decide)
  have h22 : Entails.eval a c1335 := derived1335 a h
  have h23 : Entails.eval a c316 := h 315 (by decide)
  have h24 : Entails.eval a c206 := h 205 (by decide)
  have h25 : Entails.eval a c312 := h 311 (by decide)
  have h26 : Entails.eval a c296 := h 295 (by decide)
  have h27 : Entails.eval a c244 := h 243 (by decide)
  have h28 : Entails.eval a c27 := h 26 (by decide)
  have h29 : Entails.eval a c163 := h 162 (by decide)
  have h30 : Entails.eval a c155 := h 154 (by decide)
  have h31 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c43, some c42, some c152, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 57) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c43, c42, c152] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c174, some c180, some c87, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 57) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c174, c180, c87] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c174 := h 173 (by decide)
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨46, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1388, some c1132, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 57) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c1388, c1132] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c1388 := derived1388 a h
  have h1 : Entails.eval a c1132 := derived1132 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1391 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨47, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨46, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c242, some c295, some c288, some c371, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 57) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c208, c242, c295, c288, c371] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c242 := h 241 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨46, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c241, some c24, some c164, some c331, some c74, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 57) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c241, c24, c164, c331, c74] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c331 := h 330 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1393 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c28, some c982, some c156, some c217, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1393 : lratChecker f1393 p1393 = .success := by decide +kernel
theorem unsat1393 : Unsatisfiable (PosFin 57) f1393 := by
  apply lratCheckerSound f1393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1393
  · intro a ha; simp [p1393] at ha; subst a; trivial
  · exact checked1393
theorem derived1393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1393 := by
  apply localUnsat_implies_entails f1393 [c8, c28, c982, c156, c217] c1393 unsat1393 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c982 := derived982 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1394 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c1275, some c18, some c1137, some c1389, some c1147, some c1346, some c43, some c152, some c209, some c139, some c313, some c1380, some c87, some c135, some c1391, some c318, some c1393, some c715, some c243, some c1392, some c293, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 57) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c107, c1275, c18, c1137, c1389, c1147, c1346, c43, c152, c209, c139, c313, c1380, c87, c135, c1391, c318, c1393, c715, c243, c1392, c293] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c1275 := derived1275 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c1137 := derived1137 a h
  have h4 : Entails.eval a c1389 := derived1389 a h
  have h5 : Entails.eval a c1147 := derived1147 a h
  have h6 : Entails.eval a c1346 := derived1346 a h
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c1380 := derived1380 a h
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c1391 := derived1391 a h
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c1393 := derived1393 a h
  have h18 : Entails.eval a c715 := derived715 a h
  have h19 : Entails.eval a c243 := h 242 (by decide)
  have h20 : Entails.eval a c1392 := derived1392 a h
  have h21 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c1380, some c37, some c874, some c873, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 57) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c262, c1380, c37, c874, c873] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c874 := derived874 a h
  have h4 : Entails.eval a c873 := derived873 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1387, some c108, some c107, some c1275, some c1378, some c1137, some c1389, some c1346, some c1147, some c1395, some c1390, some c205, some c1394, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 57) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c1387, c108, c107, c1275, c1378, c1137, c1389, c1346, c1147, c1395, c1390, c205, c1394] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c1387 := derived1387 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1378 := derived1378 a h
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1389 := derived1389 a h
  have h7 : Entails.eval a c1346 := derived1346 a h
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c1395 := derived1395 a h
  have h10 : Entails.eval a c1390 := derived1390 a h
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1387, some c107, some c108, some c1346, some c1378, some c1137, some c1275, some c1147, some c1395, some c1393, some c1389, some c243, some c1396, some c45, some c135, some c146, some c87, some c317, some c316, some c139, some c293, some c43, some c241, some c207, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 57) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c1387, c107, c108, c1346, c1378, c1137, c1275, c1147, c1395, c1393, c1389, c243, c1396, c45, c135, c146, c87, c317, c316, c139, c293, c43, c241, c207] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c1387 := derived1387 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1346 := derived1346 a h
  have h4 : Entails.eval a c1378 := derived1378 a h
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1275 := derived1275 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c1395 := derived1395 a h
  have h9 : Entails.eval a c1393 := derived1393 a h
  have h10 : Entails.eval a c1389 := derived1389 a h
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c1396 := derived1396 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c87 := h 86 (by decide)
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c293 := h 292 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c241 := h 240 (by decide)
  have h23 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c43, some c152, some c209, some c139, some c148, some c313, some c87, some c244, some c291, some c715, some c987, some c295, some c242, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 57) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c205, c43, c152, c209, c139, c148, c313, c87, c244, c291, c715, c987, c295, c242] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c244 := h 243 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c715 := derived715 a h
  have h11 : Entails.eval a c987 := derived987 a h
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨26, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c148, some c316, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 57) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c152, c148, c316] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1378, some c108, some c1387, some c107, some c1275, some c1346, some c1137, some c1147, some c1395, some c1393, some c1397, some c200, some c4, some c17, some c1398, some c45, some c1399, some c43, some c206, some c267, some c5, some c25, some c153, some c217, some c160, some c73, some c64, some c274, some c350, some c259, some c136, some c62, some c241, some c47, some c138, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 57) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c1378, c108, c1387, c107, c1275, c1346, c1137, c1147, c1395, c1393, c1397, c200, c4, c17, c1398, c45, c1399, c43, c206, c267, c5, c25, c153, c217, c160, c73, c64, c274, c350, c259, c136, c62, c241, c47, c138] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c1378 := derived1378 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c1346 := derived1346 a h
  have h6 : Entails.eval a c1137 := derived1137 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c1395 := derived1395 a h
  have h9 : Entails.eval a c1393 := derived1393 a h
  have h10 : Entails.eval a c1397 := derived1397 a h
  have h11 : Entails.eval a c200 := h 199 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c1398 := derived1398 a h
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c1399 := derived1399 a h
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c267 := h 266 (by decide)
  have h20 : Entails.eval a c5 := h 4 (by decide)
  have h21 : Entails.eval a c25 := h 24 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  have h23 : Entails.eval a c217 := h 216 (by decide)
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c73 := h 72 (by decide)
  have h26 : Entails.eval a c64 := h 63 (by decide)
  have h27 : Entails.eval a c274 := h 273 (by decide)
  have h28 : Entails.eval a c350 := h 349 (by decide)
  have h29 : Entails.eval a c259 := h 258 (by decide)
  have h30 : Entails.eval a c136 := h 135 (by decide)
  have h31 : Entails.eval a c62 := h 61 (by decide)
  have h32 : Entails.eval a c241 := h 240 (by decide)
  have h33 : Entails.eval a c47 := h 46 (by decide)
  have h34 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1400, some c1378, some c108, some c7, some c16, some c1332, some c201, some c110, some c1147, some c1346, some c1395, some c113, some c122, some c42, some c268, some c146, some c152, some c208, some c319, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 57) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c1400, c1378, c108, c7, c16, c1332, c201, c110, c1147, c1346, c1395, c113, c122, c42, c268, c146, c152, c208, c319] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c1400 := derived1400 a h
  have h1 : Entails.eval a c1378 := derived1378 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c1346 := derived1346 a h
  have h10 : Entails.eval a c1395 := derived1395 a h
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c208 := h 207 (by decide)
  have h18 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨48, by decide⟩, true), (⟨19, by decide⟩, false), (⟨43, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c295, some c238, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 57) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c208, c295, c238] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨19, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c209, some c289, some c239, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 57) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c209, c289, c239] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c209 := h 208 (by decide)
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1403, some c312, some c208, some c288, some c238, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 57) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c1403, c312, c208, c288, c238] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c1403 := derived1403 a h
  have h1 : Entails.eval a c312 := h 311 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c42, some c146, some c138, some c78, some c83, some c170, some c1404, some c122, some c262, some c1380, some c8, some c27, some c209, some c889, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 57) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c1147, c42, c146, c138, c78, c83, c170, c1404, c122, c262, c1380, c8, c27, c209, c889] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c1404 := derived1404 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c1380 := derived1380 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c889 := derived889 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c267, some c36, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 57) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c268, c267, c36] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c1406, some c208, some c25, some c166, some c269, some c72, some c76, some c217, some c350, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 57) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c122, c1406, c208, c25, c166, c269, c72, c76, c217, c350] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c1406 := derived1406 a h
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1378, some c108, some c1405, some c18, some c1407, some c1335, some c1380, some c8, some c28, some c27, some c168, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 57) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1147, c1378, c108, c1405, c18, c1407, c1335, c1380, c8, c28, c27, c168] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1378 := derived1378 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1405 := derived1405 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c1407 := derived1407 a h
  have h6 : Entails.eval a c1335 := derived1335 a h
  have h7 : Entails.eval a c1380 := derived1380 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1401, some c1400, some c1378, some c108, some c1275, some c1346, some c1147, some c1408, some c113, some c142, some c262, some c1380, some c39, some c8, some c27, some c209, some c1406, some c889, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 57) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c1401, c1400, c1378, c108, c1275, c1346, c1147, c1408, c113, c142, c262, c1380, c39, c8, c27, c209, c1406, c889] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c1401 := derived1401 a h
  have h1 : Entails.eval a c1400 := derived1400 a h
  have h2 : Entails.eval a c1378 := derived1378 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c1346 := derived1346 a h
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c1408 := derived1408 a h
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c1380 := derived1380 a h
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c1406 := derived1406 a h
  have h17 : Entails.eval a c889 := derived889 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c1407, some c1406, some c5, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 57) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c122, c1407, c1406, c5] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c1407 := derived1407 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c312, some c889, some c208, some c27, some c261, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 57) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c312, c889, c208, c27, c261] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c312 := h 311 (by decide)
  have h1 : Entails.eval a c889 := derived889 a h
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1409, some c106, some c1378, some c44, some c108, some c1400, some c1401, some c1410, some c1335, some c120, some c202, some c18, some c1147, some c115, some c1411, some c209, some c261, some c208, some c25, some c318, some c166, some c269, some c278, some c213, some c72, some c63, some c76, some c223, some c164, some c196, some c247, some c194, some c350, some c853, some c136, some c505, some c335, some c102, some c174, some c138, some c372, some c377, some c81, some c364, some c289, some c80, some c397, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 57) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1409, c106, c1378, c44, c108, c1400, c1401, c1410, c1335, c120, c202, c18, c1147, c115, c1411, c209, c261, c208, c25, c318, c166, c269, c278, c213, c72, c63, c76, c223, c164, c196, c247, c194, c350, c853, c136, c505, c335, c102, c174, c138, c372, c377, c81, c364, c289, c80, c397] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1409 := derived1409 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1378 := derived1378 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1400 := derived1400 a h
  have h6 : Entails.eval a c1401 := derived1401 a h
  have h7 : Entails.eval a c1410 := derived1410 a h
  have h8 : Entails.eval a c1335 := derived1335 a h
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c1147 := derived1147 a h
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c1411 := derived1411 a h
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c208 := h 207 (by decide)
  have h18 : Entails.eval a c25 := h 24 (by decide)
  have h19 : Entails.eval a c318 := h 317 (by decide)
  have h20 : Entails.eval a c166 := h 165 (by decide)
  have h21 : Entails.eval a c269 := h 268 (by decide)
  have h22 : Entails.eval a c278 := h 277 (by decide)
  have h23 : Entails.eval a c213 := h 212 (by decide)
  have h24 : Entails.eval a c72 := h 71 (by decide)
  have h25 : Entails.eval a c63 := h 62 (by decide)
  have h26 : Entails.eval a c76 := h 75 (by decide)
  have h27 : Entails.eval a c223 := h 222 (by decide)
  have h28 : Entails.eval a c164 := h 163 (by decide)
  have h29 : Entails.eval a c196 := h 195 (by decide)
  have h30 : Entails.eval a c247 := h 246 (by decide)
  have h31 : Entails.eval a c194 := h 193 (by decide)
  have h32 : Entails.eval a c350 := h 349 (by decide)
  have h33 : Entails.eval a c853 := derived853 a h
  have h34 : Entails.eval a c136 := h 135 (by decide)
  have h35 : Entails.eval a c505 := derived505 a h
  have h36 : Entails.eval a c335 := h 334 (by decide)
  have h37 : Entails.eval a c102 := h 101 (by decide)
  have h38 : Entails.eval a c174 := h 173 (by decide)
  have h39 : Entails.eval a c138 := h 137 (by decide)
  have h40 : Entails.eval a c372 := h 371 (by decide)
  have h41 : Entails.eval a c377 := h 376 (by decide)
  have h42 : Entails.eval a c81 := h 80 (by decide)
  have h43 : Entails.eval a c364 := h 363 (by decide)
  have h44 : Entails.eval a c289 := h 288 (by decide)
  have h45 : Entails.eval a c80 := h 79 (by decide)
  have h46 : Entails.eval a c397 := h 396 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1409, some c106, some c1401, some c1400, some c1378, some c108, some c44, some c1410, some c1335, some c120, some c202, some c18, some c1412, some c1406, some c208, some c25, some c539, some c166, some c269, some c72, some c63, some c352, some c255, some c247, some c335, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 57) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c1409, c106, c1401, c1400, c1378, c108, c44, c1410, c1335, c120, c202, c18, c1412, c1406, c208, c25, c539, c166, c269, c72, c63, c352, c255, c247, c335] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c1409 := derived1409 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1401 := derived1401 a h
  have h3 : Entails.eval a c1400 := derived1400 a h
  have h4 : Entails.eval a c1378 := derived1378 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c1410 := derived1410 a h
  have h8 : Entails.eval a c1335 := derived1335 a h
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c1412 := derived1412 a h
  have h13 : Entails.eval a c1406 := derived1406 a h
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c539 := derived539 a h
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c72 := h 71 (by decide)
  have h20 : Entails.eval a c63 := h 62 (by decide)
  have h21 : Entails.eval a c352 := h 351 (by decide)
  have h22 : Entails.eval a c255 := h 254 (by decide)
  have h23 : Entails.eval a c247 := h 246 (by decide)
  have h24 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1413

end CochromaticTwenty.Certificates.B16_0_2Enumerating
