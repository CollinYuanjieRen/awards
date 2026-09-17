import MerLeanExperiment.Certificates.B16_8_2.Steps1800_1899

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2281 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨13, by decide⟩, true), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2281 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c1241, some c1051, some c178, some c155, some c373, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2281 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2281 : lratChecker f2281 p2281 = .success := by decide +kernel
theorem unsat2281 : Unsatisfiable (PosFin 57) f2281 := by
  apply lratCheckerSound f2281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2281
  · intro a ha; simp [p2281] at ha; subst a; trivial
  · exact checked2281
theorem derived2281 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2281 := by
  apply localUnsat_implies_entails f2281 [c2201, c1241, c1051, c178, c155, c373] c2281 unsat2281 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c1241 := derived1241 a h
  have h2 : Entails.eval a c1051 := derived1051 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2282 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2282 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2271, some c366, some c101, some c2253, some c2268, some c2259, some c2273, some c2280, some c1239, some c376, some c1118, some c67, some c1491, some c2279, some c314, some c194, some c2281, some c2241, some c2136, some c332, some c31, some c196, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2282 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2282 : lratChecker f2282 p2282 = .success := by decide +kernel
theorem unsat2282 : Unsatisfiable (PosFin 57) f2282 := by
  apply lratCheckerSound f2282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2282
  · intro a ha; simp [p2282] at ha; subst a; trivial
  · exact checked2282
theorem derived2282 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2282 := by
  apply localUnsat_implies_entails f2282 [c2271, c366, c101, c2253, c2268, c2259, c2273, c2280, c1239, c376, c1118, c67, c1491, c2279, c314, c194, c2281, c2241, c2136, c332, c31, c196] c2282 unsat2282 (by rfl) a
  have h0 : Entails.eval a c2271 := derived2271 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2253 := derived2253 a h
  have h4 : Entails.eval a c2268 := derived2268 a h
  have h5 : Entails.eval a c2259 := derived2259 a h
  have h6 : Entails.eval a c2273 := derived2273 a h
  have h7 : Entails.eval a c2280 := derived2280 a h
  have h8 : Entails.eval a c1239 := derived1239 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c1118 := derived1118 a h
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c1491 := derived1491 a h
  have h13 : Entails.eval a c2279 := derived2279 a h
  have h14 : Entails.eval a c314 := h 313 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c2281 := derived2281 a h
  have h17 : Entails.eval a c2241 := derived2241 a h
  have h18 : Entails.eval a c2136 := derived2136 a h
  have h19 : Entails.eval a c332 := h 331 (by decide)
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2283 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨45, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2283 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2025, some c2050, some c2026, some c273, some c336, some c322, some c271, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2283 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2283 : lratChecker f2283 p2283 = .success := by decide +kernel
theorem unsat2283 : Unsatisfiable (PosFin 57) f2283 := by
  apply lratCheckerSound f2283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2283
  · intro a ha; simp [p2283] at ha; subst a; trivial
  · exact checked2283
theorem derived2283 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2283 := by
  apply localUnsat_implies_entails f2283 [c2025, c2050, c2026, c273, c336, c322, c271] c2283 unsat2283 (by rfl) a
  have h0 : Entails.eval a c2025 := derived2025 a h
  have h1 : Entails.eval a c2050 := derived2050 a h
  have h2 : Entails.eval a c2026 := derived2026 a h
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c336 := h 335 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2284 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2284 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2259, some c2253, some c101, some c2268, some c2271, some c366, some c2282, some c66, some c1239, some c376, some c1118, some c67, some c1491, some c2281, some c841, some c2241, some c2136, some c155, some c16, some c167, some c2283, some c314, some c332, some c313, some c2238, some c271, some c2047, some c282, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2284 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2284 : lratChecker f2284 p2284 = .success := by decide +kernel
theorem unsat2284 : Unsatisfiable (PosFin 57) f2284 := by
  apply lratCheckerSound f2284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2284
  · intro a ha; simp [p2284] at ha; subst a; trivial
  · exact checked2284
theorem derived2284 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2284 := by
  apply localUnsat_implies_entails f2284 [c2201, c2259, c2253, c101, c2268, c2271, c366, c2282, c66, c1239, c376, c1118, c67, c1491, c2281, c841, c2241, c2136, c155, c16, c167, c2283, c314, c332, c313, c2238, c271, c2047, c282] c2284 unsat2284 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2259 := derived2259 a h
  have h2 : Entails.eval a c2253 := derived2253 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c2268 := derived2268 a h
  have h5 : Entails.eval a c2271 := derived2271 a h
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c2282 := derived2282 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c1239 := derived1239 a h
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c1118 := derived1118 a h
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c1491 := derived1491 a h
  have h14 : Entails.eval a c2281 := derived2281 a h
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c2241 := derived2241 a h
  have h17 : Entails.eval a c2136 := derived2136 a h
  have h18 : Entails.eval a c155 := h 154 (by decide)
  have h19 : Entails.eval a c16 := h 15 (by decide)
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c2283 := derived2283 a h
  have h22 : Entails.eval a c314 := h 313 (by decide)
  have h23 : Entails.eval a c332 := h 331 (by decide)
  have h24 : Entails.eval a c313 := h 312 (by decide)
  have h25 : Entails.eval a c2238 := derived2238 a h
  have h26 : Entails.eval a c271 := h 270 (by decide)
  have h27 : Entails.eval a c2047 := derived2047 a h
  have h28 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2285 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2285 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c968, some c1118, some c11, some c9, some c164, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2285 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2285 : lratChecker f2285 p2285 = .success := by decide +kernel
theorem unsat2285 : Unsatisfiable (PosFin 57) f2285 := by
  apply lratCheckerSound f2285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2285
  · intro a ha; simp [p2285] at ha; subst a; trivial
  · exact checked2285
theorem derived2285 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2285 := by
  apply localUnsat_implies_entails f2285 [c2201, c104, c968, c1118, c11, c9, c164] c2285 unsat2285 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2286 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2286 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2209, some c34, some c320, some c317, some c59, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2286 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2286 : lratChecker f2286 p2286 = .success := by decide +kernel
theorem unsat2286 : Unsatisfiable (PosFin 57) f2286 := by
  apply lratCheckerSound f2286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2286
  · intro a ha; simp [p2286] at ha; subst a; trivial
  · exact checked2286
theorem derived2286 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2286 := by
  apply localUnsat_implies_entails f2286 [c2209, c34, c320, c317, c59] c2286 unsat2286 (by rfl) a
  have h0 : Entails.eval a c2209 := derived2209 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2287 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2287 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2253, some c2259, some c2285, some c2284, some c2068, some c2027, some c2279, some c2268, some c370, some c1039, some c2286, some c2261, some c2267, some c2262, some c2067, some c1118, some c1491, some c179, some c373, some c329, some c364, some c1202, some c330, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2287 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2287 : lratChecker f2287 p2287 = .success := by decide +kernel
theorem unsat2287 : Unsatisfiable (PosFin 57) f2287 := by
  apply lratCheckerSound f2287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2287
  · intro a ha; simp [p2287] at ha; subst a; trivial
  · exact checked2287
theorem derived2287 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2287 := by
  apply localUnsat_implies_entails f2287 [c101, c2253, c2259, c2285, c2284, c2068, c2027, c2279, c2268, c370, c1039, c2286, c2261, c2267, c2262, c2067, c1118, c1491, c179, c373, c329, c364, c1202, c330] c2287 unsat2287 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c2259 := derived2259 a h
  have h3 : Entails.eval a c2285 := derived2285 a h
  have h4 : Entails.eval a c2284 := derived2284 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c2279 := derived2279 a h
  have h8 : Entails.eval a c2268 := derived2268 a h
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c1039 := derived1039 a h
  have h11 : Entails.eval a c2286 := derived2286 a h
  have h12 : Entails.eval a c2261 := derived2261 a h
  have h13 : Entails.eval a c2267 := derived2267 a h
  have h14 : Entails.eval a c2262 := derived2262 a h
  have h15 : Entails.eval a c2067 := derived2067 a h
  have h16 : Entails.eval a c1118 := derived1118 a h
  have h17 : Entails.eval a c1491 := derived1491 a h
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  have h20 : Entails.eval a c329 := h 328 (by decide)
  have h21 : Entails.eval a c364 := h 363 (by decide)
  have h22 : Entails.eval a c1202 := derived1202 a h
  have h23 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2288 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2288 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2287, some c101, some c2253, some c2259, some c2285, some c2284, some c2027, some c2268, some c376, some c379, some c968, some c2275, some c2260, some c2203, some c172, some c1051, some c155, some c164, some c1103, some c184, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2288 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2288 : lratChecker f2288 p2288 = .success := by decide +kernel
theorem unsat2288 : Unsatisfiable (PosFin 57) f2288 := by
  apply lratCheckerSound f2288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2288
  · intro a ha; simp [p2288] at ha; subst a; trivial
  · exact checked2288
theorem derived2288 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2288 := by
  apply localUnsat_implies_entails f2288 [c2201, c2287, c101, c2253, c2259, c2285, c2284, c2027, c2268, c376, c379, c968, c2275, c2260, c2203, c172, c1051, c155, c164, c1103, c184] c2288 unsat2288 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2287 := derived2287 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2253 := derived2253 a h
  have h4 : Entails.eval a c2259 := derived2259 a h
  have h5 : Entails.eval a c2285 := derived2285 a h
  have h6 : Entails.eval a c2284 := derived2284 a h
  have h7 : Entails.eval a c2027 := derived2027 a h
  have h8 : Entails.eval a c2268 := derived2268 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c968 := derived968 a h
  have h12 : Entails.eval a c2275 := derived2275 a h
  have h13 : Entails.eval a c2260 := derived2260 a h
  have h14 : Entails.eval a c2203 := derived2203 a h
  have h15 : Entails.eval a c172 := h 171 (by decide)
  have h16 : Entails.eval a c1051 := derived1051 a h
  have h17 : Entails.eval a c155 := h 154 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c1103 := derived1103 a h
  have h20 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2289 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨11, by decide⟩, false), (⟨48, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c1491, some c72, some c156, some c1051, some c2281, some c2261, some c164, some c377, some c2072, some c184, some c172, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2289 : lratChecker f2289 p2289 = .success := by decide +kernel
theorem unsat2289 : Unsatisfiable (PosFin 57) f2289 := by
  apply lratCheckerSound f2289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2289
  · intro a ha; simp [p2289] at ha; subst a; trivial
  · exact checked2289
theorem derived2289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2289 := by
  apply localUnsat_implies_entails f2289 [c2201, c1491, c72, c156, c1051, c2281, c2261, c164, c377, c2072, c184, c172] c2289 unsat2289 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c1491 := derived1491 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c1051 := derived1051 a h
  have h5 : Entails.eval a c2281 := derived2281 a h
  have h6 : Entails.eval a c2261 := derived2261 a h
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c2072 := derived2072 a h
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2290 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2253, some c2259, some c2285, some c2268, some c2284, some c2068, some c2027, some c2277, some c2279, some c2287, some c2288, some c1118, some c1491, some c2289, some c841, some c374, some c1039, some c292, some c332, some c155, some c40, some c196, some c16, some c32, some c165, some c167, some c2278, some c13, some c35, some c178, some c322, some c289, some c271, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked2290 : lratChecker f2290 p2290 = .success := by decide +kernel
theorem unsat2290 : Unsatisfiable (PosFin 57) f2290 := by
  apply lratCheckerSound f2290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2290
  · intro a ha; simp [p2290] at ha; subst a; trivial
  · exact checked2290
theorem derived2290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2290 := by
  apply localUnsat_implies_entails f2290 [c2201, c101, c2253, c2259, c2285, c2268, c2284, c2068, c2027, c2277, c2279, c2287, c2288, c1118, c1491, c2289, c841, c374, c1039, c292, c332, c155, c40, c196, c16, c32, c165, c167, c2278, c13, c35, c178, c322, c289, c271] c2290 unsat2290 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2253 := derived2253 a h
  have h3 : Entails.eval a c2259 := derived2259 a h
  have h4 : Entails.eval a c2285 := derived2285 a h
  have h5 : Entails.eval a c2268 := derived2268 a h
  have h6 : Entails.eval a c2284 := derived2284 a h
  have h7 : Entails.eval a c2068 := derived2068 a h
  have h8 : Entails.eval a c2027 := derived2027 a h
  have h9 : Entails.eval a c2277 := derived2277 a h
  have h10 : Entails.eval a c2279 := derived2279 a h
  have h11 : Entails.eval a c2287 := derived2287 a h
  have h12 : Entails.eval a c2288 := derived2288 a h
  have h13 : Entails.eval a c1118 := derived1118 a h
  have h14 : Entails.eval a c1491 := derived1491 a h
  have h15 : Entails.eval a c2289 := derived2289 a h
  have h16 : Entails.eval a c841 := derived841 a h
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c1039 := derived1039 a h
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c332 := h 331 (by decide)
  have h21 : Entails.eval a c155 := h 154 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  have h23 : Entails.eval a c196 := h 195 (by decide)
  have h24 : Entails.eval a c16 := h 15 (by decide)
  have h25 : Entails.eval a c32 := h 31 (by decide)
  have h26 : Entails.eval a c165 := h 164 (by decide)
  have h27 : Entails.eval a c167 := h 166 (by decide)
  have h28 : Entails.eval a c2278 := derived2278 a h
  have h29 : Entails.eval a c13 := h 12 (by decide)
  have h30 : Entails.eval a c35 := h 34 (by decide)
  have h31 : Entails.eval a c178 := h 177 (by decide)
  have h32 : Entails.eval a c322 := h 321 (by decide)
  have h33 : Entails.eval a c289 := h 288 (by decide)
  have h34 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2291 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2290, some c2167, some c101, some c367, some c2035, some c2068, some c2093, some c2027, some c370, some c152, some c1226, some c2277, some c2279, some c166, some c12, some c69, some c289, some c329, some c37, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2291 : lratChecker f2291 p2291 = .success := by decide +kernel
theorem unsat2291 : Unsatisfiable (PosFin 57) f2291 := by
  apply lratCheckerSound f2291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2291
  · intro a ha; simp [p2291] at ha; subst a; trivial
  · exact checked2291
theorem derived2291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2291 := by
  apply localUnsat_implies_entails f2291 [c2290, c2167, c101, c367, c2035, c2068, c2093, c2027, c370, c152, c1226, c2277, c2279, c166, c12, c69, c289, c329, c37] c2291 unsat2291 (by rfl) a
  have h0 : Entails.eval a c2290 := derived2290 a h
  have h1 : Entails.eval a c2167 := derived2167 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c2093 := derived2093 a h
  have h7 : Entails.eval a c2027 := derived2027 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c1226 := derived1226 a h
  have h11 : Entails.eval a c2277 := derived2277 a h
  have h12 : Entails.eval a c2279 := derived2279 a h
  have h13 : Entails.eval a c166 := h 165 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2292 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2290, some c2167, some c2291, some c2094, some c368, some c2095, some c79, some c13, some c15, some c176, some c163, some c167, some c188, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2292 : lratChecker f2292 p2292 = .success := by decide +kernel
theorem unsat2292 : Unsatisfiable (PosFin 57) f2292 := by
  apply lratCheckerSound f2292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2292
  · intro a ha; simp [p2292] at ha; subst a; trivial
  · exact checked2292
theorem derived2292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2292 := by
  apply localUnsat_implies_entails f2292 [c2290, c2167, c2291, c2094, c368, c2095, c79, c13, c15, c176, c163, c167, c188] c2292 unsat2292 (by rfl) a
  have h0 : Entails.eval a c2290 := derived2290 a h
  have h1 : Entails.eval a c2167 := derived2167 a h
  have h2 : Entails.eval a c2291 := derived2291 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c2095 := derived2095 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c167 := h 166 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2293 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2290, some c2167, some c2292, some c76, some c2093, some c2291, some c1241, some c2096, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2293 : lratChecker f2293 p2293 = .success := by decide +kernel
theorem unsat2293 : Unsatisfiable (PosFin 57) f2293 := by
  apply lratCheckerSound f2293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2293
  · intro a ha; simp [p2293] at ha; subst a; trivial
  · exact checked2293
theorem derived2293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2293 := by
  apply localUnsat_implies_entails f2293 [c101, c2290, c2167, c2292, c76, c2093, c2291, c1241, c2096] c2293 unsat2293 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2292 := derived2292 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c2093 := derived2093 a h
  have h6 : Entails.eval a c2291 := derived2291 a h
  have h7 : Entails.eval a c1241 := derived1241 a h
  have h8 : Entails.eval a c2096 := derived2096 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2294 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c2167, some c2292, some c76, some c66, some c2291, some c2094, some c2293, some c2203, some c2241, some c154, some c15, some c13, some c167, some c176, some c14, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2294 : lratChecker f2294 p2294 = .success := by decide +kernel
theorem unsat2294 : Unsatisfiable (PosFin 57) f2294 := by
  apply lratCheckerSound f2294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2294
  · intro a ha; simp [p2294] at ha; subst a; trivial
  · exact checked2294
theorem derived2294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2294 := by
  apply localUnsat_implies_entails f2294 [c2201, c101, c2290, c2167, c2292, c76, c66, c2291, c2094, c2293, c2203, c2241, c154, c15, c13, c167, c176, c14] c2294 unsat2294 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c2167 := derived2167 a h
  have h4 : Entails.eval a c2292 := derived2292 a h
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c2291 := derived2291 a h
  have h8 : Entails.eval a c2094 := derived2094 a h
  have h9 : Entails.eval a c2293 := derived2293 a h
  have h10 : Entails.eval a c2203 := derived2203 a h
  have h11 : Entails.eval a c2241 := derived2241 a h
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2295 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨33, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2093, some c2294, some c314, some c2290, some c315, some c2167, some c2292, some c76, some c66, some c2291, some c2094, some c1241, some c1051, some c176, some c180, some c12, some c2073, some c160, some c194, some c272, some c29, some c222, some c275, some c199, some c2061, some c122, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2295 : lratChecker f2295 p2295 = .success := by decide +kernel
theorem unsat2295 : Unsatisfiable (PosFin 57) f2295 := by
  apply lratCheckerSound f2295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2295
  · intro a ha; simp [p2295] at ha; subst a; trivial
  · exact checked2295
theorem derived2295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2295 := by
  apply localUnsat_implies_entails f2295 [c2201, c101, c2093, c2294, c314, c2290, c315, c2167, c2292, c76, c66, c2291, c2094, c1241, c1051, c176, c180, c12, c2073, c160, c194, c272, c29, c222, c275, c199, c2061, c122] c2295 unsat2295 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2093 := derived2093 a h
  have h3 : Entails.eval a c2294 := derived2294 a h
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c2290 := derived2290 a h
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c2167 := derived2167 a h
  have h8 : Entails.eval a c2292 := derived2292 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c2291 := derived2291 a h
  have h12 : Entails.eval a c2094 := derived2094 a h
  have h13 : Entails.eval a c1241 := derived1241 a h
  have h14 : Entails.eval a c1051 := derived1051 a h
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c180 := h 179 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c2073 := derived2073 a h
  have h19 : Entails.eval a c160 := h 159 (by decide)
  have h20 : Entails.eval a c194 := h 193 (by decide)
  have h21 : Entails.eval a c272 := h 271 (by decide)
  have h22 : Entails.eval a c29 := h 28 (by decide)
  have h23 : Entails.eval a c222 := h 221 (by decide)
  have h24 : Entails.eval a c275 := h 274 (by decide)
  have h25 : Entails.eval a c199 := h 198 (by decide)
  have h26 : Entails.eval a c2061 := derived2061 a h
  have h27 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2296 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c12, some c14, some c176, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2296 : lratChecker f2296 p2296 = .success := by decide +kernel
theorem unsat2296 : Unsatisfiable (PosFin 57) f2296 := by
  apply lratCheckerSound f2296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2296
  · intro a ha; simp [p2296] at ha; subst a; trivial
  · exact checked2296
theorem derived2296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2296 := by
  apply localUnsat_implies_entails f2296 [c2201, c12, c14, c176] c2296 unsat2296 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2297 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2203, some c2241, some c16, some c15, some c180, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2297 : lratChecker f2297 p2297 = .success := by decide +kernel
theorem unsat2297 : Unsatisfiable (PosFin 57) f2297 := by
  apply lratCheckerSound f2297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2297
  · intro a ha; simp [p2297] at ha; subst a; trivial
  · exact checked2297
theorem derived2297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2297 := by
  apply localUnsat_implies_entails f2297 [c2201, c2203, c2241, c16, c15, c180] c2297 unsat2297 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2203 := derived2203 a h
  have h2 : Entails.eval a c2241 := derived2241 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2298 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2290, some c2167, some c2291, some c2094, some c101, some c2093, some c2292, some c66, some c76, some c2294, some c2296, some c167, some c160, some c2297, some c186, some c1051, some c2295, some c176, some c180, some c2050, some c2228, some c138, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2298 : lratChecker f2298 p2298 = .success := by decide +kernel
theorem unsat2298 : Unsatisfiable (PosFin 57) f2298 := by
  apply lratCheckerSound f2298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2298
  · intro a ha; simp [p2298] at ha; subst a; trivial
  · exact checked2298
theorem derived2298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2298 := by
  apply localUnsat_implies_entails f2298 [c2201, c2290, c2167, c2291, c2094, c101, c2093, c2292, c66, c76, c2294, c2296, c167, c160, c2297, c186, c1051, c2295, c176, c180, c2050, c2228, c138] c2298 unsat2298 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2291 := derived2291 a h
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c2093 := derived2093 a h
  have h7 : Entails.eval a c2292 := derived2292 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c2294 := derived2294 a h
  have h11 : Entails.eval a c2296 := derived2296 a h
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c2297 := derived2297 a h
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c1051 := derived1051 a h
  have h17 : Entails.eval a c2295 := derived2295 a h
  have h18 : Entails.eval a c176 := h 175 (by decide)
  have h19 : Entails.eval a c180 := h 179 (by decide)
  have h20 : Entails.eval a c2050 := derived2050 a h
  have h21 : Entails.eval a c2228 := derived2228 a h
  have h22 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2299 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2279, some c2277, some c2273, some c2100, some c275, some c314, some c272, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2299 : lratChecker f2299 p2299 = .success := by decide +kernel
theorem unsat2299 : Unsatisfiable (PosFin 57) f2299 := by
  apply lratCheckerSound f2299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2299
  · intro a ha; simp [p2299] at ha; subst a; trivial
  · exact checked2299
theorem derived2299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2299 := by
  apply localUnsat_implies_entails f2299 [c2279, c2277, c2273, c2100, c275, c314, c272] c2299 unsat2299 (by rfl) a
  have h0 : Entails.eval a c2279 := derived2279 a h
  have h1 : Entails.eval a c2277 := derived2277 a h
  have h2 : Entails.eval a c2273 := derived2273 a h
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2300 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨46, by decide⟩, false), (⟨12, by decide⟩, false), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2290, some c2167, some c101, some c12, some c187, some c83, some c69, some c16, some c163, some c2277, some c2279, some c2299, some c2035, some c329, some c289, some c37, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2300 : lratChecker f2300 p2300 = .success := by decide +kernel
theorem unsat2300 : Unsatisfiable (PosFin 57) f2300 := by
  apply lratCheckerSound f2300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2300
  · intro a ha; simp [p2300] at ha; subst a; trivial
  · exact checked2300
theorem derived2300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2300 := by
  apply localUnsat_implies_entails f2300 [c2201, c2290, c2167, c101, c12, c187, c83, c69, c16, c163, c2277, c2279, c2299, c2035, c329, c289, c37] c2300 unsat2300 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c2277 := derived2277 a h
  have h11 : Entails.eval a c2279 := derived2279 a h
  have h12 : Entails.eval a c2299 := derived2299 a h
  have h13 : Entails.eval a c2035 := derived2035 a h
  have h14 : Entails.eval a c329 := h 328 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2301 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false), (⟨12, by decide⟩, false), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2290, some c2167, some c2094, some c101, some c2300, some c153, some c167, some c2297, some c16, some c2066, some c79, some c2277, some c2279, some c292, some c289, some c332, some c329, some c271, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2301 : lratChecker f2301 p2301 = .success := by decide +kernel
theorem unsat2301 : Unsatisfiable (PosFin 57) f2301 := by
  apply lratCheckerSound f2301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2301
  · intro a ha; simp [p2301] at ha; subst a; trivial
  · exact checked2301
theorem derived2301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2301 := by
  apply localUnsat_implies_entails f2301 [c2201, c2290, c2167, c2094, c101, c2300, c153, c167, c2297, c16, c2066, c79, c2277, c2279, c292, c289, c332, c329, c271] c2301 unsat2301 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c2300 := derived2300 a h
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c2297 := derived2297 a h
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c2066 := derived2066 a h
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c2277 := derived2277 a h
  have h13 : Entails.eval a c2279 := derived2279 a h
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  have h16 : Entails.eval a c332 := h 331 (by decide)
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2302 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2290, some c101, some c2167, some c2291, some c2094, some c2298, some c152, some c1226, some c361, some c2203, some c154, some c180, some c2301, some c66, some c76, some c2297, some c2296, some c167, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2302 : lratChecker f2302 p2302 = .success := by decide +kernel
theorem unsat2302 : Unsatisfiable (PosFin 57) f2302 := by
  apply lratCheckerSound f2302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2302
  · intro a ha; simp [p2302] at ha; subst a; trivial
  · exact checked2302
theorem derived2302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2302 := by
  apply localUnsat_implies_entails f2302 [c2290, c101, c2167, c2291, c2094, c2298, c152, c1226, c361, c2203, c154, c180, c2301, c66, c76, c2297, c2296, c167] c2302 unsat2302 (by rfl) a
  have h0 : Entails.eval a c2290 := derived2290 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2291 := derived2291 a h
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c2298 := derived2298 a h
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c1226 := derived1226 a h
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c2203 := derived2203 a h
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c2301 := derived2301 a h
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c2297 := derived2297 a h
  have h16 : Entails.eval a c2296 := derived2296 a h
  have h17 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2303 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c104, some c2290, some c367, some c2035, some c2068, some c2220, some c2222, some c330, some c2223, some c1085, some c69, some c2224, some c2061, some c44, some c290, some c284, some c194, some c192, some c29, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2303 : lratChecker f2303 p2303 = .success := by decide +kernel
theorem unsat2303 : Unsatisfiable (PosFin 57) f2303 := by
  apply lratCheckerSound f2303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2303
  · intro a ha; simp [p2303] at ha; subst a; trivial
  · exact checked2303
theorem derived2303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2303 := by
  apply localUnsat_implies_entails f2303 [c2201, c101, c104, c2290, c367, c2035, c2068, c2220, c2222, c330, c2223, c1085, c69, c2224, c2061, c44, c290, c284, c194, c192, c29] c2303 unsat2303 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2290 := derived2290 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2068 := derived2068 a h
  have h7 : Entails.eval a c2220 := derived2220 a h
  have h8 : Entails.eval a c2222 := derived2222 a h
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c2223 := derived2223 a h
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c2224 := derived2224 a h
  have h14 : Entails.eval a c2061 := derived2061 a h
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c290 := h 289 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c194 := h 193 (by decide)
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2304 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c177, some c2112, some c15, some c11, some c95, some c176, some c1697, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2304 : lratChecker f2304 p2304 = .success := by decide +kernel
theorem unsat2304 : Unsatisfiable (PosFin 57) f2304 := by
  apply lratCheckerSound f2304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2304
  · intro a ha; simp [p2304] at ha; subst a; trivial
  · exact checked2304
theorem derived2304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2304 := by
  apply localUnsat_implies_entails f2304 [c2201, c104, c177, c2112, c15, c11, c95, c176, c1697] c2304 unsat2304 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c2112 := derived2112 a h
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c1697 := derived1697 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2305 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2220, some c2265, some c2223, some c320, some c2025, some c2221, some c289, some c44, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2305 : lratChecker f2305 p2305 = .success := by decide +kernel
theorem unsat2305 : Unsatisfiable (PosFin 57) f2305 := by
  apply lratCheckerSound f2305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2305
  · intro a ha; simp [p2305] at ha; subst a; trivial
  · exact checked2305
theorem derived2305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2305 := by
  apply localUnsat_implies_entails f2305 [c2220, c2265, c2223, c320, c2025, c2221, c289, c44] c2305 unsat2305 (by rfl) a
  have h0 : Entails.eval a c2220 := derived2220 a h
  have h1 : Entails.eval a c2265 := derived2265 a h
  have h2 : Entails.eval a c2223 := derived2223 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c2025 := derived2025 a h
  have h5 : Entails.eval a c2221 := derived2221 a h
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2306 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c2035, some c2068, some c2305, some c69, some c2220, some c2025, some c2050, some c119, some c320, some c954, some c269, some c284, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2306 : lratChecker f2306 p2306 = .success := by decide +kernel
theorem unsat2306 : Unsatisfiable (PosFin 57) f2306 := by
  apply lratCheckerSound f2306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2306
  · intro a ha; simp [p2306] at ha; subst a; trivial
  · exact checked2306
theorem derived2306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2306 := by
  apply localUnsat_implies_entails f2306 [c367, c2035, c2068, c2305, c69, c2220, c2025, c2050, c119, c320, c954, c269, c284] c2306 unsat2306 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c2035 := derived2035 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c2305 := derived2305 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c2220 := derived2220 a h
  have h6 : Entails.eval a c2025 := derived2025 a h
  have h7 : Entails.eval a c2050 := derived2050 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c320 := h 319 (by decide)
  have h10 : Entails.eval a c954 := derived954 a h
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2307 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c367, some c2068, some c370, some c2035, some c2302, some c104, some c976, some c2220, some c2303, some c154, some c13, some c2304, some c841, some c176, some c11, some c158, some c2305, some c1085, some c69, some c2136, some c2306, some c332, some c2221, some c269, some c44, some c284, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2307 : lratChecker f2307 p2307 = .success := by decide +kernel
theorem unsat2307 : Unsatisfiable (PosFin 57) f2307 := by
  apply lratCheckerSound f2307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2307
  · intro a ha; simp [p2307] at ha; subst a; trivial
  · exact checked2307
theorem derived2307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2307 := by
  apply localUnsat_implies_entails f2307 [c2201, c101, c2290, c367, c2068, c370, c2035, c2302, c104, c976, c2220, c2303, c154, c13, c2304, c841, c176, c11, c158, c2305, c1085, c69, c2136, c2306, c332, c2221, c269, c44, c284] c2307 unsat2307 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c2068 := derived2068 a h
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c2302 := derived2302 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c976 := derived976 a h
  have h10 : Entails.eval a c2220 := derived2220 a h
  have h11 : Entails.eval a c2303 := derived2303 a h
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  have h14 : Entails.eval a c2304 := derived2304 a h
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c2305 := derived2305 a h
  have h20 : Entails.eval a c1085 := derived1085 a h
  have h21 : Entails.eval a c69 := h 68 (by decide)
  have h22 : Entails.eval a c2136 := derived2136 a h
  have h23 : Entails.eval a c2306 := derived2306 a h
  have h24 : Entails.eval a c332 := h 331 (by decide)
  have h25 : Entails.eval a c2221 := derived2221 a h
  have h26 : Entails.eval a c269 := h 268 (by decide)
  have h27 : Entails.eval a c44 := h 43 (by decide)
  have h28 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2308 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2302, some c104, some c2290, some c101, some c367, some c2035, some c2068, some c370, some c2307, some c152, some c1226, some c9, some c162, some c372, some c69, some c2265, some c317, some c2046, some c277, some c2061, some c44, some c289, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2308 : lratChecker f2308 p2308 = .success := by decide +kernel
theorem unsat2308 : Unsatisfiable (PosFin 57) f2308 := by
  apply lratCheckerSound f2308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2308
  · intro a ha; simp [p2308] at ha; subst a; trivial
  · exact checked2308
theorem derived2308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2308 := by
  apply localUnsat_implies_entails f2308 [c2201, c2302, c104, c2290, c101, c367, c2035, c2068, c370, c2307, c152, c1226, c9, c162, c372, c69, c2265, c317, c2046, c277, c2061, c44, c289] c2308 unsat2308 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2302 := derived2302 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2290 := derived2290 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c2068 := derived2068 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c2307 := derived2307 a h
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c1226 := derived1226 a h
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c2265 := derived2265 a h
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c2046 := derived2046 a h
  have h19 : Entails.eval a c277 := h 276 (by decide)
  have h20 : Entails.eval a c2061 := derived2061 a h
  have h21 : Entails.eval a c44 := h 43 (by decide)
  have h22 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2309 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2025, some c2050, some c290, some c1047, some c335, some c194, some c211, some c29, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2309 : lratChecker f2309 p2309 = .success := by decide +kernel
theorem unsat2309 : Unsatisfiable (PosFin 57) f2309 := by
  apply lratCheckerSound f2309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2309
  · intro a ha; simp [p2309] at ha; subst a; trivial
  · exact checked2309
theorem derived2309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2309 := by
  apply localUnsat_implies_entails f2309 [c101, c2025, c2050, c290, c1047, c335, c194, c211, c29] c2309 unsat2309 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2025 := derived2025 a h
  have h2 : Entails.eval a c2050 := derived2050 a h
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c1047 := derived1047 a h
  have h5 : Entails.eval a c335 := h 334 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c211 := h 210 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2310 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c369, some c101, some c2302, some c104, some c976, some c2308, some c2290, some c1241, some c1051, some c359, some c154, some c162, some c9, some c176, some c2008, some c380, some c69, some c365, some c2035, some c2220, some c2309, some c330, some c331, some c2224, some c2061, some c290, some c291, some c272, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2310 : lratChecker f2310 p2310 = .success := by decide +kernel
theorem unsat2310 : Unsatisfiable (PosFin 57) f2310 := by
  apply lratCheckerSound f2310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2310
  · intro a ha; simp [p2310] at ha; subst a; trivial
  · exact checked2310
theorem derived2310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2310 := by
  apply localUnsat_implies_entails f2310 [c2201, c369, c101, c2302, c104, c976, c2308, c2290, c1241, c1051, c359, c154, c162, c9, c176, c2008, c380, c69, c365, c2035, c2220, c2309, c330, c331, c2224, c2061, c290, c291, c272] c2310 unsat2310 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2302 := derived2302 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c976 := derived976 a h
  have h6 : Entails.eval a c2308 := derived2308 a h
  have h7 : Entails.eval a c2290 := derived2290 a h
  have h8 : Entails.eval a c1241 := derived1241 a h
  have h9 : Entails.eval a c1051 := derived1051 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c2008 := derived2008 a h
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c365 := h 364 (by decide)
  have h19 : Entails.eval a c2035 := derived2035 a h
  have h20 : Entails.eval a c2220 := derived2220 a h
  have h21 : Entails.eval a c2309 := derived2309 a h
  have h22 : Entails.eval a c330 := h 329 (by decide)
  have h23 : Entails.eval a c331 := h 330 (by decide)
  have h24 : Entails.eval a c2224 := derived2224 a h
  have h25 : Entails.eval a c2061 := derived2061 a h
  have h26 : Entails.eval a c290 := h 289 (by decide)
  have h27 : Entails.eval a c291 := h 290 (by decide)
  have h28 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2311 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2302, some c104, some c976, some c2308, some c2290, some c369, some c2310, some c841, some c2203, some c2111, some c154, some c2115, some c13, some c11, some c176, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2311 : lratChecker f2311 p2311 = .success := by decide +kernel
theorem unsat2311 : Unsatisfiable (PosFin 57) f2311 := by
  apply lratCheckerSound f2311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2311
  · intro a ha; simp [p2311] at ha; subst a; trivial
  · exact checked2311
theorem derived2311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2311 := by
  apply localUnsat_implies_entails f2311 [c2201, c101, c2302, c104, c976, c2308, c2290, c369, c2310, c841, c2203, c2111, c154, c2115, c13, c11, c176] c2311 unsat2311 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2302 := derived2302 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c976 := derived976 a h
  have h5 : Entails.eval a c2308 := derived2308 a h
  have h6 : Entails.eval a c2290 := derived2290 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c2310 := derived2310 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c2203 := derived2203 a h
  have h11 : Entails.eval a c2111 := derived2111 a h
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c2115 := derived2115 a h
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2312 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c76, some c365, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2312 : lratChecker f2312 p2312 = .success := by decide +kernel
theorem unsat2312 : Unsatisfiable (PosFin 57) f2312 := by
  apply lratCheckerSound f2312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2312
  · intro a ha; simp [p2312] at ha; subst a; trivial
  · exact checked2312
theorem derived2312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2312 := by
  apply localUnsat_implies_entails f2312 [c2068, c76, c365] c2312 unsat2312 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2313 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨39, by decide⟩, true), (⟨43, by decide⟩, false), (⟨30, by decide⟩, true), (⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c319, some c266, some c272, some c283, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2313 : lratChecker f2313 p2313 = .success := by decide +kernel
theorem unsat2313 : Unsatisfiable (PosFin 57) f2313 := by
  apply lratCheckerSound f2313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2313
  · intro a ha; simp [p2313] at ha; subst a; trivial
  · exact checked2313
theorem derived2313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2313 := by
  apply localUnsat_implies_entails f2313 [c317, c319, c266, c272, c283] c2313 unsat2313 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2314 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2308, some c101, some c2290, some c2302, some c104, some c2312, some c2311, some c361, some c841, some c1226, some c2203, some c180, some c154, some c152, some c9, some c174, some c365, some c2273, some c1414, some c69, some c16, some c960, some c167, some c2132, some c2313, some c56, some c2051, some c338, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2314 : lratChecker f2314 p2314 = .success := by decide +kernel
theorem unsat2314 : Unsatisfiable (PosFin 57) f2314 := by
  apply lratCheckerSound f2314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2314
  · intro a ha; simp [p2314] at ha; subst a; trivial
  · exact checked2314
theorem derived2314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2314 := by
  apply localUnsat_implies_entails f2314 [c2201, c2308, c101, c2290, c2302, c104, c2312, c2311, c361, c841, c1226, c2203, c180, c154, c152, c9, c174, c365, c2273, c1414, c69, c16, c960, c167, c2132, c2313, c56, c2051, c338] c2314 unsat2314 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2308 := derived2308 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2290 := derived2290 a h
  have h4 : Entails.eval a c2302 := derived2302 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c2312 := derived2312 a h
  have h7 : Entails.eval a c2311 := derived2311 a h
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c1226 := derived1226 a h
  have h11 : Entails.eval a c2203 := derived2203 a h
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c154 := h 153 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c174 := h 173 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c2273 := derived2273 a h
  have h19 : Entails.eval a c1414 := derived1414 a h
  have h20 : Entails.eval a c69 := h 68 (by decide)
  have h21 : Entails.eval a c16 := h 15 (by decide)
  have h22 : Entails.eval a c960 := derived960 a h
  have h23 : Entails.eval a c167 := h 166 (by decide)
  have h24 : Entails.eval a c2132 := derived2132 a h
  have h25 : Entails.eval a c2313 := derived2313 a h
  have h26 : Entails.eval a c56 := h 55 (by decide)
  have h27 : Entails.eval a c2051 := derived2051 a h
  have h28 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2315 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c863, some c144, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2315 : lratChecker f2315 p2315 = .success := by decide +kernel
theorem unsat2315 : Unsatisfiable (PosFin 57) f2315 := by
  apply lratCheckerSound f2315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2315
  · intro a ha; simp [p2315] at ha; subst a; trivial
  · exact checked2315
theorem derived2315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2315 := by
  apply localUnsat_implies_entails f2315 [c37, c863, c144] c2315 unsat2315 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2316 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2290, some c101, some c2302, some c104, some c2308, some c2312, some c2311, some c152, some c1226, some c361, some c9, some c841, some c2203, some c174, some c154, some c180, some c2314, some c2035, some c2134, some c372, some c83, some c69, some c16, some c2265, some c167, some c317, some c319, some c2315, some c298, some c289, some c266, some c2061, some c279, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked2316 : lratChecker f2316 p2316 = .success := by decide +kernel
theorem unsat2316 : Unsatisfiable (PosFin 57) f2316 := by
  apply lratCheckerSound f2316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2316
  · intro a ha; simp [p2316] at ha; subst a; trivial
  · exact checked2316
theorem derived2316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2316 := by
  apply localUnsat_implies_entails f2316 [c2201, c2290, c101, c2302, c104, c2308, c2312, c2311, c152, c1226, c361, c9, c841, c2203, c174, c154, c180, c2314, c2035, c2134, c372, c83, c69, c16, c2265, c167, c317, c319, c2315, c298, c289, c266, c2061, c279] c2316 unsat2316 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2302 := derived2302 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2308 := derived2308 a h
  have h6 : Entails.eval a c2312 := derived2312 a h
  have h7 : Entails.eval a c2311 := derived2311 a h
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c1226 := derived1226 a h
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c2203 := derived2203 a h
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c180 := h 179 (by decide)
  have h17 : Entails.eval a c2314 := derived2314 a h
  have h18 : Entails.eval a c2035 := derived2035 a h
  have h19 : Entails.eval a c2134 := derived2134 a h
  have h20 : Entails.eval a c372 := h 371 (by decide)
  have h21 : Entails.eval a c83 := h 82 (by decide)
  have h22 : Entails.eval a c69 := h 68 (by decide)
  have h23 : Entails.eval a c16 := h 15 (by decide)
  have h24 : Entails.eval a c2265 := derived2265 a h
  have h25 : Entails.eval a c167 := h 166 (by decide)
  have h26 : Entails.eval a c317 := h 316 (by decide)
  have h27 : Entails.eval a c319 := h 318 (by decide)
  have h28 : Entails.eval a c2315 := derived2315 a h
  have h29 : Entails.eval a c298 := h 297 (by decide)
  have h30 : Entails.eval a c289 := h 288 (by decide)
  have h31 : Entails.eval a c266 := h 265 (by decide)
  have h32 : Entails.eval a c2061 := derived2061 a h
  have h33 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2317 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨45, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c369, some c67, some c379, some c363, some c362, some c2203, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2317 : lratChecker f2317 p2317 = .success := by decide +kernel
theorem unsat2317 : Unsatisfiable (PosFin 57) f2317 := by
  apply lratCheckerSound f2317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2317
  · intro a ha; simp [p2317] at ha; subst a; trivial
  · exact checked2317
theorem derived2317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2317 := by
  apply localUnsat_implies_entails f2317 [c368, c369, c67, c379, c363, c362, c2203] c2317 unsat2317 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c362 := h 361 (by decide)
  have h6 : Entails.eval a c2203 := derived2203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2318 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2136, some c2025, some c2050, some c2026, some c289, some c336, some c142, some c271, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2318 : lratChecker f2318 p2318 = .success := by decide +kernel
theorem unsat2318 : Unsatisfiable (PosFin 57) f2318 := by
  apply lratCheckerSound f2318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2318
  · intro a ha; simp [p2318] at ha; subst a; trivial
  · exact checked2318
theorem derived2318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2318 := by
  apply localUnsat_implies_entails f2318 [c2136, c2025, c2050, c2026, c289, c336, c142, c271] c2318 unsat2318 (by rfl) a
  have h0 : Entails.eval a c2136 := derived2136 a h
  have h1 : Entails.eval a c2025 := derived2025 a h
  have h2 : Entails.eval a c2050 := derived2050 a h
  have h3 : Entails.eval a c2026 := derived2026 a h
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c142 := h 141 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2319 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2316, some c101, some c2290, some c2167, some c2093, some c367, some c2317, some c66, some c376, some c67, some c377, some c2094, some c2268, some c154, some c362, some c1241, some c13, some c2241, some c2297, some c2136, some c2099, some c167, some c2318, some c332, some c2071, some c196, some c32, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2319 : lratChecker f2319 p2319 = .success := by decide +kernel
theorem unsat2319 : Unsatisfiable (PosFin 57) f2319 := by
  apply lratCheckerSound f2319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2319
  · intro a ha; simp [p2319] at ha; subst a; trivial
  · exact checked2319
theorem derived2319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2319 := by
  apply localUnsat_implies_entails f2319 [c2201, c2316, c101, c2290, c2167, c2093, c367, c2317, c66, c376, c67, c377, c2094, c2268, c154, c362, c1241, c13, c2241, c2297, c2136, c2099, c167, c2318, c332, c2071, c196, c32] c2319 unsat2319 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2316 := derived2316 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2290 := derived2290 a h
  have h4 : Entails.eval a c2167 := derived2167 a h
  have h5 : Entails.eval a c2093 := derived2093 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c2317 := derived2317 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c2094 := derived2094 a h
  have h13 : Entails.eval a c2268 := derived2268 a h
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c362 := h 361 (by decide)
  have h16 : Entails.eval a c1241 := derived1241 a h
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c2241 := derived2241 a h
  have h19 : Entails.eval a c2297 := derived2297 a h
  have h20 : Entails.eval a c2136 := derived2136 a h
  have h21 : Entails.eval a c2099 := derived2099 a h
  have h22 : Entails.eval a c167 := h 166 (by decide)
  have h23 : Entails.eval a c2318 := derived2318 a h
  have h24 : Entails.eval a c332 := h 331 (by decide)
  have h25 : Entails.eval a c2071 := derived2071 a h
  have h26 : Entails.eval a c196 := h 195 (by decide)
  have h27 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2320 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c1241, some c1051, some c180, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2320 : lratChecker f2320 p2320 = .success := by decide +kernel
theorem unsat2320 : Unsatisfiable (PosFin 57) f2320 := by
  apply lratCheckerSound f2320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2320
  · intro a ha; simp [p2320] at ha; subst a; trivial
  · exact checked2320
theorem derived2320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2320 := by
  apply localUnsat_implies_entails f2320 [c2201, c1241, c1051, c180] c2320 unsat2320 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c1241 := derived1241 a h
  have h2 : Entails.eval a c1051 := derived1051 a h
  have h3 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2321 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2241, some c2025, some c2050, some c2026, some c275, some c274, some c336, some c137, some c196, some c952, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2321 : lratChecker f2321 p2321 = .success := by decide +kernel
theorem unsat2321 : Unsatisfiable (PosFin 57) f2321 := by
  apply lratCheckerSound f2321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2321
  · intro a ha; simp [p2321] at ha; subst a; trivial
  · exact checked2321
theorem derived2321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2321 := by
  apply localUnsat_implies_entails f2321 [c2201, c2241, c2025, c2050, c2026, c275, c274, c336, c137, c196, c952] c2321 unsat2321 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2241 := derived2241 a h
  have h2 : Entails.eval a c2025 := derived2025 a h
  have h3 : Entails.eval a c2050 := derived2050 a h
  have h4 : Entails.eval a c2026 := derived2026 a h
  have h5 : Entails.eval a c275 := h 274 (by decide)
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c952 := derived952 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2322 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2316, some c2268, some c2290, some c2167, some c2093, some c367, some c2094, some c2317, some c66, some c76, some c376, some c377, some c67, some c2319, some c2320, some c2241, some c2297, some c2136, some c167, some c12, some c14, some c2099, some c2321, some c332, some c2071, some c196, some c32, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2322 : lratChecker f2322 p2322 = .success := by decide +kernel
theorem unsat2322 : Unsatisfiable (PosFin 57) f2322 := by
  apply lratCheckerSound f2322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2322
  · intro a ha; simp [p2322] at ha; subst a; trivial
  · exact checked2322
theorem derived2322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2322 := by
  apply localUnsat_implies_entails f2322 [c2201, c101, c2316, c2268, c2290, c2167, c2093, c367, c2094, c2317, c66, c76, c376, c377, c67, c2319, c2320, c2241, c2297, c2136, c167, c12, c14, c2099, c2321, c332, c2071, c196, c32] c2322 unsat2322 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2316 := derived2316 a h
  have h3 : Entails.eval a c2268 := derived2268 a h
  have h4 : Entails.eval a c2290 := derived2290 a h
  have h5 : Entails.eval a c2167 := derived2167 a h
  have h6 : Entails.eval a c2093 := derived2093 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c2094 := derived2094 a h
  have h9 : Entails.eval a c2317 := derived2317 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c2319 := derived2319 a h
  have h16 : Entails.eval a c2320 := derived2320 a h
  have h17 : Entails.eval a c2241 := derived2241 a h
  have h18 : Entails.eval a c2297 := derived2297 a h
  have h19 : Entails.eval a c2136 := derived2136 a h
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c2099 := derived2099 a h
  have h24 : Entails.eval a c2321 := derived2321 a h
  have h25 : Entails.eval a c332 := h 331 (by decide)
  have h26 : Entails.eval a c2071 := derived2071 a h
  have h27 : Entails.eval a c196 := h 195 (by decide)
  have h28 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2323 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c330, some c290, some c291, some c331, some c272, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2323 : lratChecker f2323 p2323 = .success := by decide +kernel
theorem unsat2323 : Unsatisfiable (PosFin 57) f2323 := by
  apply lratCheckerSound f2323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2323
  · intro a ha; simp [p2323] at ha; subst a; trivial
  · exact checked2323
theorem derived2323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2323 := by
  apply localUnsat_implies_entails f2323 [c330, c290, c291, c331, c272] c2323 unsat2323 (by rfl) a
  have h0 : Entails.eval a c330 := h 329 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c331 := h 330 (by decide)
  have h4 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2324 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c113, some c120, some c136, some c196, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2324 : lratChecker f2324 p2324 = .success := by decide +kernel
theorem unsat2324 : Unsatisfiable (PosFin 57) f2324 := by
  apply lratCheckerSound f2324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2324
  · intro a ha; simp [p2324] at ha; subst a; trivial
  · exact checked2324
theorem derived2324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2324 := by
  apply localUnsat_implies_entails f2324 [c159, c113, c120, c136, c196] c2324 unsat2324 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2325 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2290, some c367, some c2068, some c2027, some c2286, some c2279, some c2277, some c370, some c2322, some c2316, some c2268, some c2167, some c290, some c330, some c194, some c29, some c31, some c2324, some c13, some c166, some c12, some c69, some c1202, some c329, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2325 : lratChecker f2325 p2325 = .success := by decide +kernel
theorem unsat2325 : Unsatisfiable (PosFin 57) f2325 := by
  apply lratCheckerSound f2325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2325
  · intro a ha; simp [p2325] at ha; subst a; trivial
  · exact checked2325
theorem derived2325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2325 := by
  apply localUnsat_implies_entails f2325 [c101, c2290, c367, c2068, c2027, c2286, c2279, c2277, c370, c2322, c2316, c2268, c2167, c290, c330, c194, c29, c31, c2324, c13, c166, c12, c69, c1202, c329] c2325 unsat2325 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2068 := derived2068 a h
  have h4 : Entails.eval a c2027 := derived2027 a h
  have h5 : Entails.eval a c2286 := derived2286 a h
  have h6 : Entails.eval a c2279 := derived2279 a h
  have h7 : Entails.eval a c2277 := derived2277 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c2322 := derived2322 a h
  have h10 : Entails.eval a c2316 := derived2316 a h
  have h11 : Entails.eval a c2268 := derived2268 a h
  have h12 : Entails.eval a c2167 := derived2167 a h
  have h13 : Entails.eval a c290 := h 289 (by decide)
  have h14 : Entails.eval a c330 := h 329 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c2324 := derived2324 a h
  have h19 : Entails.eval a c13 := h 12 (by decide)
  have h20 : Entails.eval a c166 := h 165 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c69 := h 68 (by decide)
  have h23 : Entails.eval a c1202 := derived1202 a h
  have h24 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2326 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2322, some c101, some c2316, some c2268, some c2290, some c2167, some c367, some c2068, some c2027, some c370, some c2277, some c2279, some c2325, some c154, some c362, some c13, some c289, some c329, some c159, some c134, some c118, some c270, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2326 : lratChecker f2326 p2326 = .success := by decide +kernel
theorem unsat2326 : Unsatisfiable (PosFin 57) f2326 := by
  apply lratCheckerSound f2326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2326
  · intro a ha; simp [p2326] at ha; subst a; trivial
  · exact checked2326
theorem derived2326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2326 := by
  apply localUnsat_implies_entails f2326 [c2322, c101, c2316, c2268, c2290, c2167, c367, c2068, c2027, c370, c2277, c2279, c2325, c154, c362, c13, c289, c329, c159, c134, c118, c270] c2326 unsat2326 (by rfl) a
  have h0 : Entails.eval a c2322 := derived2322 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2316 := derived2316 a h
  have h3 : Entails.eval a c2268 := derived2268 a h
  have h4 : Entails.eval a c2290 := derived2290 a h
  have h5 : Entails.eval a c2167 := derived2167 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c2068 := derived2068 a h
  have h8 : Entails.eval a c2027 := derived2027 a h
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c2277 := derived2277 a h
  have h11 : Entails.eval a c2279 := derived2279 a h
  have h12 : Entails.eval a c2325 := derived2325 a h
  have h13 : Entails.eval a c154 := h 153 (by decide)
  have h14 : Entails.eval a c362 := h 361 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2327 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2268, some c2167, some c2203, some c363, some c379, some c67, some c2277, some c2279, some c2100, some c275, some c290, some c330, some c272, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2327 : lratChecker f2327 p2327 = .success := by decide +kernel
theorem unsat2327 : Unsatisfiable (PosFin 57) f2327 := by
  apply lratCheckerSound f2327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2327
  · intro a ha; simp [p2327] at ha; subst a; trivial
  · exact checked2327
theorem derived2327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2327 := by
  apply localUnsat_implies_entails f2327 [c2268, c2167, c2203, c363, c379, c67, c2277, c2279, c2100, c275, c290, c330, c272] c2327 unsat2327 (by rfl) a
  have h0 : Entails.eval a c2268 := derived2268 a h
  have h1 : Entails.eval a c2167 := derived2167 a h
  have h2 : Entails.eval a c2203 := derived2203 a h
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c2277 := derived2277 a h
  have h7 : Entails.eval a c2279 := derived2279 a h
  have h8 : Entails.eval a c2100 := derived2100 a h
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2328 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨54, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2326, some c2290, some c2167, some c2094, some c2320, some c2322, some c101, some c2316, some c2268, some c154, some c362, some c13, some c379, some c165, some c67, some c15, some c2277, some c2279, some c292, some c332, some c40, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2328 : lratChecker f2328 p2328 = .success := by decide +kernel
theorem unsat2328 : Unsatisfiable (PosFin 57) f2328 := by
  apply lratCheckerSound f2328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2328
  · intro a ha; simp [p2328] at ha; subst a; trivial
  · exact checked2328
theorem derived2328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2328 := by
  apply localUnsat_implies_entails f2328 [c2326, c2290, c2167, c2094, c2320, c2322, c101, c2316, c2268, c154, c362, c13, c379, c165, c67, c15, c2277, c2279, c292, c332, c40] c2328 unsat2328 (by rfl) a
  have h0 : Entails.eval a c2326 := derived2326 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c2320 := derived2320 a h
  have h5 : Entails.eval a c2322 := derived2322 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c2316 := derived2316 a h
  have h8 : Entails.eval a c2268 := derived2268 a h
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c362 := h 361 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c2277 := derived2277 a h
  have h17 : Entails.eval a c2279 := derived2279 a h
  have h18 : Entails.eval a c292 := h 291 (by decide)
  have h19 : Entails.eval a c332 := h 331 (by decide)
  have h20 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2329 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2290, some c2167, some c2326, some c2094, some c2322, some c2316, some c101, some c2327, some c2328, some c2299, some c67, some c79, some c379, some c968, some c153, some c12, some c14, some c165, some c180, some c15, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2329 : lratChecker f2329 p2329 = .success := by decide +kernel
theorem unsat2329 : Unsatisfiable (PosFin 57) f2329 := by
  apply lratCheckerSound f2329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2329
  · intro a ha; simp [p2329] at ha; subst a; trivial
  · exact checked2329
theorem derived2329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2329 := by
  apply localUnsat_implies_entails f2329 [c2201, c2290, c2167, c2326, c2094, c2322, c2316, c101, c2327, c2328, c2299, c67, c79, c379, c968, c153, c12, c14, c165, c180, c15] c2329 unsat2329 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2326 := derived2326 a h
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c2322 := derived2322 a h
  have h6 : Entails.eval a c2316 := derived2316 a h
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c2327 := derived2327 a h
  have h9 : Entails.eval a c2328 := derived2328 a h
  have h10 : Entails.eval a c2299 := derived2299 a h
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c165 := h 164 (by decide)
  have h19 : Entails.eval a c180 := h 179 (by decide)
  have h20 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2330 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2290, some c2167, some c2326, some c2094, some c2322, some c101, some c2316, some c2268, some c66, some c76, some c1239, some c2320, some c2297, some c165, some c167, some c12, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2330 : lratChecker f2330 p2330 = .success := by decide +kernel
theorem unsat2330 : Unsatisfiable (PosFin 57) f2330 := by
  apply lratCheckerSound f2330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2330
  · intro a ha; simp [p2330] at ha; subst a; trivial
  · exact checked2330
theorem derived2330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2330 := by
  apply localUnsat_implies_entails f2330 [c2290, c2167, c2326, c2094, c2322, c101, c2316, c2268, c66, c76, c1239, c2320, c2297, c165, c167, c12] c2330 unsat2330 (by rfl) a
  have h0 : Entails.eval a c2290 := derived2290 a h
  have h1 : Entails.eval a c2167 := derived2167 a h
  have h2 : Entails.eval a c2326 := derived2326 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c2322 := derived2322 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c2316 := derived2316 a h
  have h7 : Entails.eval a c2268 := derived2268 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c1239 := derived1239 a h
  have h11 : Entails.eval a c2320 := derived2320 a h
  have h12 : Entails.eval a c2297 := derived2297 a h
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2331 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false), (⟨48, by decide⟩, true), (⟨49, by decide⟩, false), (⟨45, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2203, some c290, some c330, some c363, some c1202, some c329, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2331 : lratChecker f2331 p2331 = .success := by decide +kernel
theorem unsat2331 : Unsatisfiable (PosFin 57) f2331 := by
  apply lratCheckerSound f2331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2331
  · intro a ha; simp [p2331] at ha; subst a; trivial
  · exact checked2331
theorem derived2331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2331 := by
  apply localUnsat_implies_entails f2331 [c2203, c290, c330, c363, c1202, c329] c2331 unsat2331 (by rfl) a
  have h0 : Entails.eval a c2203 := derived2203 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c1202 := derived1202 a h
  have h5 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2332 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c15, some c16, some c180, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2332 : lratChecker f2332 p2332 = .success := by decide +kernel
theorem unsat2332 : Unsatisfiable (PosFin 57) f2332 := by
  apply lratCheckerSound f2332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2332
  · intro a ha; simp [p2332] at ha; subst a; trivial
  · exact checked2332
theorem derived2332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2332 := by
  apply localUnsat_implies_entails f2332 [c2201, c15, c16, c180] c2332 unsat2332 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2333 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2316, some c2290, some c101, some c2167, some c2268, some c2322, some c2326, some c2094, some c2330, some c2329, some c2027, some c2277, some c2279, some c2331, some c2320, some c2328, some c292, some c332, some c40, some c2332, some c165, some c13, some c2301, some c180, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2333 : lratChecker f2333 p2333 = .success := by decide +kernel
theorem unsat2333 : Unsatisfiable (PosFin 57) f2333 := by
  apply lratCheckerSound f2333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2333
  · intro a ha; simp [p2333] at ha; subst a; trivial
  · exact checked2333
theorem derived2333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2333 := by
  apply localUnsat_implies_entails f2333 [c2316, c2290, c101, c2167, c2268, c2322, c2326, c2094, c2330, c2329, c2027, c2277, c2279, c2331, c2320, c2328, c292, c332, c40, c2332, c165, c13, c2301, c180] c2333 unsat2333 (by rfl) a
  have h0 : Entails.eval a c2316 := derived2316 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2167 := derived2167 a h
  have h4 : Entails.eval a c2268 := derived2268 a h
  have h5 : Entails.eval a c2322 := derived2322 a h
  have h6 : Entails.eval a c2326 := derived2326 a h
  have h7 : Entails.eval a c2094 := derived2094 a h
  have h8 : Entails.eval a c2330 := derived2330 a h
  have h9 : Entails.eval a c2329 := derived2329 a h
  have h10 : Entails.eval a c2027 := derived2027 a h
  have h11 : Entails.eval a c2277 := derived2277 a h
  have h12 : Entails.eval a c2279 := derived2279 a h
  have h13 : Entails.eval a c2331 := derived2331 a h
  have h14 : Entails.eval a c2320 := derived2320 a h
  have h15 : Entails.eval a c2328 := derived2328 a h
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c40 := h 39 (by decide)
  have h19 : Entails.eval a c2332 := derived2332 a h
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c13 := h 12 (by decide)
  have h22 : Entails.eval a c2301 := derived2301 a h
  have h23 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2334 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c2333, some c104, some c2312, some c370, some c2316, some c968, some c976, some c2303, some c358, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2334 : lratChecker f2334 p2334 = .success := by decide +kernel
theorem unsat2334 : Unsatisfiable (PosFin 57) f2334 := by
  apply lratCheckerSound f2334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2334
  · intro a ha; simp [p2334] at ha; subst a; trivial
  · exact checked2334
theorem derived2334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2334 := by
  apply localUnsat_implies_entails f2334 [c2201, c101, c2290, c2333, c104, c2312, c370, c2316, c968, c976, c2303, c358] c2334 unsat2334 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c2333 := derived2333 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2312 := derived2312 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c2316 := derived2316 a h
  have h8 : Entails.eval a c968 := derived968 a h
  have h9 : Entails.eval a c976 := derived976 a h
  have h10 : Entails.eval a c2303 := derived2303 a h
  have h11 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2335 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c367, some c2035, some c2333, some c104, some c2316, some c377, some c1085, some c2265, some c968, some c2334, some c2125, some c11, some c9, some c967, some c173, some c112, some c964, some c137, some c139, some c249, some c25, some c214, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2335 : lratChecker f2335 p2335 = .success := by decide +kernel
theorem unsat2335 : Unsatisfiable (PosFin 57) f2335 := by
  apply lratCheckerSound f2335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2335
  · intro a ha; simp [p2335] at ha; subst a; trivial
  · exact checked2335
theorem derived2335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2335 := by
  apply localUnsat_implies_entails f2335 [c2201, c101, c2290, c367, c2035, c2333, c104, c2316, c377, c1085, c2265, c968, c2334, c2125, c11, c9, c967, c173, c112, c964, c137, c139, c249, c25, c214] c2335 unsat2335 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2333 := derived2333 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c2316 := derived2316 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c1085 := derived1085 a h
  have h10 : Entails.eval a c2265 := derived2265 a h
  have h11 : Entails.eval a c968 := derived968 a h
  have h12 : Entails.eval a c2334 := derived2334 a h
  have h13 : Entails.eval a c2125 := derived2125 a h
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c967 := derived967 a h
  have h17 : Entails.eval a c173 := h 172 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c964 := derived964 a h
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c139 := h 138 (by decide)
  have h22 : Entails.eval a c249 := h 248 (by decide)
  have h23 : Entails.eval a c25 := h 24 (by decide)
  have h24 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2336 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2290, some c367, some c2035, some c101, some c2333, some c104, some c2312, some c2316, some c968, some c377, some c1085, some c2265, some c2335, some c151, some c317, some c2046, some c277, some c2061, some c44, some c289, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2336 : lratChecker f2336 p2336 = .success := by decide +kernel
theorem unsat2336 : Unsatisfiable (PosFin 57) f2336 := by
  apply lratCheckerSound f2336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2336
  · intro a ha; simp [p2336] at ha; subst a; trivial
  · exact checked2336
theorem derived2336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2336 := by
  apply localUnsat_implies_entails f2336 [c2201, c2290, c367, c2035, c101, c2333, c104, c2312, c2316, c968, c377, c1085, c2265, c2335, c151, c317, c2046, c277, c2061, c44, c289] c2336 unsat2336 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2290 := derived2290 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2035 := derived2035 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c2333 := derived2333 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c2312 := derived2312 a h
  have h8 : Entails.eval a c2316 := derived2316 a h
  have h9 : Entails.eval a c968 := derived968 a h
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c2265 := derived2265 a h
  have h13 : Entails.eval a c2335 := derived2335 a h
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c2046 := derived2046 a h
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c2061 := derived2061 a h
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2337 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c2333, some c104, some c2312, some c2316, some c968, some c367, some c370, some c2035, some c2336, some c358, some c372, some c69, some c2265, some c317, some c2046, some c277, some c2061, some c44, some c289, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2337 : lratChecker f2337 p2337 = .success := by decide +kernel
theorem unsat2337 : Unsatisfiable (PosFin 57) f2337 := by
  apply lratCheckerSound f2337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2337
  · intro a ha; simp [p2337] at ha; subst a; trivial
  · exact checked2337
theorem derived2337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2337 := by
  apply localUnsat_implies_entails f2337 [c2201, c101, c2290, c2333, c104, c2312, c2316, c968, c367, c370, c2035, c2336, c358, c372, c69, c2265, c317, c2046, c277, c2061, c44, c289] c2337 unsat2337 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c2333 := derived2333 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2312 := derived2312 a h
  have h6 : Entails.eval a c2316 := derived2316 a h
  have h7 : Entails.eval a c968 := derived968 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c2035 := derived2035 a h
  have h11 : Entails.eval a c2336 := derived2336 a h
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c372 := h 371 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c2265 := derived2265 a h
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c2046 := derived2046 a h
  have h18 : Entails.eval a c277 := h 276 (by decide)
  have h19 : Entails.eval a c2061 := derived2061 a h
  have h20 : Entails.eval a c44 := h 43 (by decide)
  have h21 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2338 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, false), (⟨8, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c32, some c231, some c215, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2338 : lratChecker f2338 p2338 = .success := by decide +kernel
theorem unsat2338 : Unsatisfiable (PosFin 57) f2338 := by
  apply lratCheckerSound f2338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2338
  · intro a ha; simp [p2338] at ha; subst a; trivial
  · exact checked2338
theorem derived2338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2338 := by
  apply localUnsat_implies_entails f2338 [c2201, c32, c231, c215] c2338 unsat2338 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  have h3 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2339 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2337, some c101, some c2290, some c2333, some c104, some c2312, some c2316, some c968, some c377, some c2203, some c2066, some c1085, some c2008, some c1241, some c72, some c156, some c1051, some c359, some c2265, some c173, some c140, some c317, some c2338, some c964, some c116, some c138, some c29, some c31, some c217, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2339 : lratChecker f2339 p2339 = .success := by decide +kernel
theorem unsat2339 : Unsatisfiable (PosFin 57) f2339 := by
  apply lratCheckerSound f2339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2339
  · intro a ha; simp [p2339] at ha; subst a; trivial
  · exact checked2339
theorem derived2339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2339 := by
  apply localUnsat_implies_entails f2339 [c2201, c2337, c101, c2290, c2333, c104, c2312, c2316, c968, c377, c2203, c2066, c1085, c2008, c1241, c72, c156, c1051, c359, c2265, c173, c140, c317, c2338, c964, c116, c138, c29, c31, c217] c2339 unsat2339 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2337 := derived2337 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2290 := derived2290 a h
  have h4 : Entails.eval a c2333 := derived2333 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c2312 := derived2312 a h
  have h7 : Entails.eval a c2316 := derived2316 a h
  have h8 : Entails.eval a c968 := derived968 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c2203 := derived2203 a h
  have h11 : Entails.eval a c2066 := derived2066 a h
  have h12 : Entails.eval a c1085 := derived1085 a h
  have h13 : Entails.eval a c2008 := derived2008 a h
  have h14 : Entails.eval a c1241 := derived1241 a h
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c1051 := derived1051 a h
  have h18 : Entails.eval a c359 := h 358 (by decide)
  have h19 : Entails.eval a c2265 := derived2265 a h
  have h20 : Entails.eval a c173 := h 172 (by decide)
  have h21 : Entails.eval a c140 := h 139 (by decide)
  have h22 : Entails.eval a c317 := h 316 (by decide)
  have h23 : Entails.eval a c2338 := derived2338 a h
  have h24 : Entails.eval a c964 := derived964 a h
  have h25 : Entails.eval a c116 := h 115 (by decide)
  have h26 : Entails.eval a c138 := h 137 (by decide)
  have h27 : Entails.eval a c29 := h 28 (by decide)
  have h28 : Entails.eval a c31 := h 30 (by decide)
  have h29 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2340 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2339, some c2337, some c101, some c2290, some c2333, some c104, some c2312, some c2316, some c968, some c359, some c358, some c841, some c369, some c2134, some c960, some c1414, some c2332, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2340 : lratChecker f2340 p2340 = .success := by decide +kernel
theorem unsat2340 : Unsatisfiable (PosFin 57) f2340 := by
  apply lratCheckerSound f2340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2340
  · intro a ha; simp [p2340] at ha; subst a; trivial
  · exact checked2340
theorem derived2340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2340 := by
  apply localUnsat_implies_entails f2340 [c2201, c2339, c2337, c101, c2290, c2333, c104, c2312, c2316, c968, c359, c358, c841, c369, c2134, c960, c1414, c2332] c2340 unsat2340 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2339 := derived2339 a h
  have h2 : Entails.eval a c2337 := derived2337 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c2290 := derived2290 a h
  have h5 : Entails.eval a c2333 := derived2333 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c2312 := derived2312 a h
  have h8 : Entails.eval a c2316 := derived2316 a h
  have h9 : Entails.eval a c968 := derived968 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c2134 := derived2134 a h
  have h15 : Entails.eval a c960 := derived960 a h
  have h16 : Entails.eval a c1414 := derived1414 a h
  have h17 : Entails.eval a c2332 := derived2332 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2341 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c2333, some c104, some c2312, some c2339, some c2337, some c2340, some c372, some c83, some c976, some c69, some c2316, some c968, some c1240, some c9, some c165, some c15, some c154, some c2273, some c2025, some c2061, some c314, some c294, some c194, some c29, some c222, some c199, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2341 : lratChecker f2341 p2341 = .success := by decide +kernel
theorem unsat2341 : Unsatisfiable (PosFin 57) f2341 := by
  apply lratCheckerSound f2341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2341
  · intro a ha; simp [p2341] at ha; subst a; trivial
  · exact checked2341
theorem derived2341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2341 := by
  apply localUnsat_implies_entails f2341 [c2201, c101, c2290, c2333, c104, c2312, c2339, c2337, c2340, c372, c83, c976, c69, c2316, c968, c1240, c9, c165, c15, c154, c2273, c2025, c2061, c314, c294, c194, c29, c222, c199] c2341 unsat2341 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c2333 := derived2333 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2312 := derived2312 a h
  have h6 : Entails.eval a c2339 := derived2339 a h
  have h7 : Entails.eval a c2337 := derived2337 a h
  have h8 : Entails.eval a c2340 := derived2340 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  have h11 : Entails.eval a c976 := derived976 a h
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c2316 := derived2316 a h
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c1240 := derived1240 a h
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c154 := h 153 (by decide)
  have h20 : Entails.eval a c2273 := derived2273 a h
  have h21 : Entails.eval a c2025 := derived2025 a h
  have h22 : Entails.eval a c2061 := derived2061 a h
  have h23 : Entails.eval a c314 := h 313 (by decide)
  have h24 : Entails.eval a c294 := h 293 (by decide)
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c29 := h 28 (by decide)
  have h27 : Entails.eval a c222 := h 221 (by decide)
  have h28 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2342 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c2333, some c104, some c2312, some c2339, some c2337, some c2340, some c372, some c83, some c976, some c69, some c2316, some c968, some c1240, some c9, some c165, some c15, some c154, some c2273, some c2050, some c319, some c334, some c194, some c826, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2342 : lratChecker f2342 p2342 = .success := by decide +kernel
theorem unsat2342 : Unsatisfiable (PosFin 57) f2342 := by
  apply lratCheckerSound f2342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2342
  · intro a ha; simp [p2342] at ha; subst a; trivial
  · exact checked2342
theorem derived2342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2342 := by
  apply localUnsat_implies_entails f2342 [c2201, c101, c2290, c2333, c104, c2312, c2339, c2337, c2340, c372, c83, c976, c69, c2316, c968, c1240, c9, c165, c15, c154, c2273, c2050, c319, c334, c194, c826] c2342 unsat2342 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c2333 := derived2333 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2312 := derived2312 a h
  have h6 : Entails.eval a c2339 := derived2339 a h
  have h7 : Entails.eval a c2337 := derived2337 a h
  have h8 : Entails.eval a c2340 := derived2340 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  have h11 : Entails.eval a c976 := derived976 a h
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c2316 := derived2316 a h
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c1240 := derived1240 a h
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c154 := h 153 (by decide)
  have h20 : Entails.eval a c2273 := derived2273 a h
  have h21 : Entails.eval a c2050 := derived2050 a h
  have h22 : Entails.eval a c319 := h 318 (by decide)
  have h23 : Entails.eval a c334 := h 333 (by decide)
  have h24 : Entails.eval a c194 := h 193 (by decide)
  have h25 : Entails.eval a c826 := derived826 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2343 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2333, some c104, some c2337, some c2290, some c2340, some c372, some c83, some c69, some c101, some c976, some c2339, some c2312, some c2316, some c968, some c1240, some c9, some c165, some c15, some c154, some c2273, some c2341, some c275, some c2342, some c315, some c314, some c272, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2343 : lratChecker f2343 p2343 = .success := by decide +kernel
theorem unsat2343 : Unsatisfiable (PosFin 57) f2343 := by
  apply lratCheckerSound f2343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2343
  · intro a ha; simp [p2343] at ha; subst a; trivial
  · exact checked2343
theorem derived2343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2343 := by
  apply localUnsat_implies_entails f2343 [c2201, c2333, c104, c2337, c2290, c2340, c372, c83, c69, c101, c976, c2339, c2312, c2316, c968, c1240, c9, c165, c15, c154, c2273, c2341, c275, c2342, c315, c314, c272] c2343 unsat2343 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2333 := derived2333 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2337 := derived2337 a h
  have h4 : Entails.eval a c2290 := derived2290 a h
  have h5 : Entails.eval a c2340 := derived2340 a h
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c976 := derived976 a h
  have h11 : Entails.eval a c2339 := derived2339 a h
  have h12 : Entails.eval a c2312 := derived2312 a h
  have h13 : Entails.eval a c2316 := derived2316 a h
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c1240 := derived1240 a h
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c154 := h 153 (by decide)
  have h20 : Entails.eval a c2273 := derived2273 a h
  have h21 : Entails.eval a c2341 := derived2341 a h
  have h22 : Entails.eval a c275 := h 274 (by decide)
  have h23 : Entails.eval a c2342 := derived2342 a h
  have h24 : Entails.eval a c315 := h 314 (by decide)
  have h25 : Entails.eval a c314 := h 313 (by decide)
  have h26 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2344 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2339, some c2316, some c101, some c2333, some c104, some c968, some c13, some c9, some c174, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2344 : lratChecker f2344 p2344 = .success := by decide +kernel
theorem unsat2344 : Unsatisfiable (PosFin 57) f2344 := by
  apply lratCheckerSound f2344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2344
  · intro a ha; simp [p2344] at ha; subst a; trivial
  · exact checked2344
theorem derived2344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2344 := by
  apply localUnsat_implies_entails f2344 [c2201, c2339, c2316, c101, c2333, c104, c968, c13, c9, c174] c2344 unsat2344 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2339 := derived2339 a h
  have h2 : Entails.eval a c2316 := derived2316 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c2333 := derived2333 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c968 := derived968 a h
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2345 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2290, some c2316, some c2333, some c104, some c968, some c2337, some c2339, some c2340, some c372, some c976, some c83, some c2344, some c165, some c2332, some c2125, some c2008, some c2343, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2345 : lratChecker f2345 p2345 = .success := by decide +kernel
theorem unsat2345 : Unsatisfiable (PosFin 57) f2345 := by
  apply lratCheckerSound f2345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2345
  · intro a ha; simp [p2345] at ha; subst a; trivial
  · exact checked2345
theorem derived2345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2345 := by
  apply localUnsat_implies_entails f2345 [c2201, c101, c2290, c2316, c2333, c104, c968, c2337, c2339, c2340, c372, c976, c83, c2344, c165, c2332, c2125, c2008, c2343] c2345 unsat2345 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2290 := derived2290 a h
  have h3 : Entails.eval a c2316 := derived2316 a h
  have h4 : Entails.eval a c2333 := derived2333 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c968 := derived968 a h
  have h7 : Entails.eval a c2337 := derived2337 a h
  have h8 : Entails.eval a c2339 := derived2339 a h
  have h9 : Entails.eval a c2340 := derived2340 a h
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c976 := derived976 a h
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c2344 := derived2344 a h
  have h14 : Entails.eval a c165 := h 164 (by decide)
  have h15 : Entails.eval a c2332 := derived2332 a h
  have h16 : Entails.eval a c2125 := derived2125 a h
  have h17 : Entails.eval a c2008 := derived2008 a h
  have h18 : Entails.eval a c2343 := derived2343 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2346 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2028, some c295, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2346 : lratChecker f2346 p2346 = .success := by decide +kernel
theorem unsat2346 : Unsatisfiable (PosFin 57) f2346 := by
  apply lratCheckerSound f2346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2346
  · intro a ha; simp [p2346] at ha; subst a; trivial
  · exact checked2346
theorem derived2346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2346 := by
  apply localUnsat_implies_entails f2346 [c2028, c295] c2346 unsat2346 (by rfl) a
  have h0 : Entails.eval a c2028 := derived2028 a h
  have h1 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2347 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2346, some c2061, some c34, some c1688, some c335, some c2036, some c38, some c290, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2347 : lratChecker f2347 p2347 = .success := by decide +kernel
theorem unsat2347 : Unsatisfiable (PosFin 57) f2347 := by
  apply lratCheckerSound f2347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2347
  · intro a ha; simp [p2347] at ha; subst a; trivial
  · exact checked2347
theorem derived2347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2347 := by
  apply localUnsat_implies_entails f2347 [c2346, c2061, c34, c1688, c335, c2036, c38, c290] c2347 unsat2347 (by rfl) a
  have h0 : Entails.eval a c2346 := derived2346 a h
  have h1 : Entails.eval a c2061 := derived2061 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c1688 := derived1688 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c2036 := derived2036 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2348 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2347, some c2066, some c66, some c2048, some c2045, some c370, some c2049, some c78, some c34, some c317, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2348 : lratChecker f2348 p2348 = .success := by decide +kernel
theorem unsat2348 : Unsatisfiable (PosFin 57) f2348 := by
  apply lratCheckerSound f2348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2348
  · intro a ha; simp [p2348] at ha; subst a; trivial
  · exact checked2348
theorem derived2348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2348 := by
  apply localUnsat_implies_entails f2348 [c2347, c2066, c66, c2048, c2045, c370, c2049, c78, c34, c317] c2348 unsat2348 (by rfl) a
  have h0 : Entails.eval a c2347 := derived2347 a h
  have h1 : Entails.eval a c2066 := derived2066 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c2048 := derived2048 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c2049 := derived2049 a h
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2349 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c370, some c2068, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2349 : lratChecker f2349 p2349 = .success := by decide +kernel
theorem unsat2349 : Unsatisfiable (PosFin 57) f2349 := by
  apply lratCheckerSound f2349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2349
  · intro a ha; simp [p2349] at ha; subst a; trivial
  · exact checked2349
theorem derived2349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2349 := by
  apply localUnsat_implies_entails f2349 [c366, c370, c2068] c2349 unsat2349 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c2068 := derived2068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2350 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2024, some c330, some c38, some c295, some c290, some c2061, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2350 : lratChecker f2350 p2350 = .success := by decide +kernel
theorem unsat2350 : Unsatisfiable (PosFin 57) f2350 := by
  apply lratCheckerSound f2350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2350
  · intro a ha; simp [p2350] at ha; subst a; trivial
  · exact checked2350
theorem derived2350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2350 := by
  apply localUnsat_implies_entails f2350 [c2024, c330, c38, c295, c290, c2061] c2350 unsat2350 (by rfl) a
  have h0 : Entails.eval a c2024 := derived2024 a h
  have h1 : Entails.eval a c330 := h 329 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c295 := h 294 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c2061 := derived2061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2351 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c950, some c2025, some c330, some c329, some c62, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2351 : lratChecker f2351 p2351 = .success := by decide +kernel
theorem unsat2351 : Unsatisfiable (PosFin 57) f2351 := by
  apply lratCheckerSound f2351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2351
  · intro a ha; simp [p2351] at ha; subst a; trivial
  · exact checked2351
theorem derived2351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2351 := by
  apply localUnsat_implies_entails f2351 [c950, c2025, c330, c329, c62] c2351 unsat2351 (by rfl) a
  have h0 : Entails.eval a c950 := derived950 a h
  have h1 : Entails.eval a c2025 := derived2025 a h
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2352 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2349, some c70, some c2348, some c104, some c2350, some c1085, some c2351, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2352 : lratChecker f2352 p2352 = .success := by decide +kernel
theorem unsat2352 : Unsatisfiable (PosFin 57) f2352 := by
  apply lratCheckerSound f2352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2352
  · intro a ha; simp [p2352] at ha; subst a; trivial
  · exact checked2352
theorem derived2352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2352 := by
  apply localUnsat_implies_entails f2352 [c2201, c2345, c2349, c70, c2348, c104, c2350, c1085, c2351] c2352 unsat2352 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2349 := derived2349 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c2348 := derived2348 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c2350 := derived2350 a h
  have h7 : Entails.eval a c1085 := derived1085 a h
  have h8 : Entails.eval a c2351 := derived2351 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2353 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2349, some c70, some c2348, some c104, some c1753, some c2352, some c2035, some c2066, some c2041, some c2248, some c295, some c335, some c38, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2353 : lratChecker f2353 p2353 = .success := by decide +kernel
theorem unsat2353 : Unsatisfiable (PosFin 57) f2353 := by
  apply lratCheckerSound f2353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2353
  · intro a ha; simp [p2353] at ha; subst a; trivial
  · exact checked2353
theorem derived2353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2353 := by
  apply localUnsat_implies_entails f2353 [c2201, c2345, c2349, c70, c2348, c104, c1753, c2352, c2035, c2066, c2041, c2248, c295, c335, c38] c2353 unsat2353 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2349 := derived2349 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c2348 := derived2348 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c1753 := derived1753 a h
  have h7 : Entails.eval a c2352 := derived2352 a h
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c2066 := derived2066 a h
  have h10 : Entails.eval a c2041 := derived2041 a h
  have h11 : Entails.eval a c2248 := derived2248 a h
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c335 := h 334 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2354 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2347, some c2066, some c66, some c2048, some c2045, some c2049, some c2061, some c34, some c290, some c317, some c38, some c78, some c319, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2354 : lratChecker f2354 p2354 = .success := by decide +kernel
theorem unsat2354 : Unsatisfiable (PosFin 57) f2354 := by
  apply lratCheckerSound f2354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2354
  · intro a ha; simp [p2354] at ha; subst a; trivial
  · exact checked2354
theorem derived2354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2354 := by
  apply localUnsat_implies_entails f2354 [c2347, c2066, c66, c2048, c2045, c2049, c2061, c34, c290, c317, c38, c78, c319] c2354 unsat2354 (by rfl) a
  have h0 : Entails.eval a c2347 := derived2347 a h
  have h1 : Entails.eval a c2066 := derived2066 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c2048 := derived2048 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c2049 := derived2049 a h
  have h6 : Entails.eval a c2061 := derived2061 a h
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2355 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2354, some c70, some c2028, some c38, some c34, some c319, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2355 : lratChecker f2355 p2355 = .success := by decide +kernel
theorem unsat2355 : Unsatisfiable (PosFin 57) f2355 := by
  apply lratCheckerSound f2355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2355
  · intro a ha; simp [p2355] at ha; subst a; trivial
  · exact checked2355
theorem derived2355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2355 := by
  apply localUnsat_implies_entails f2355 [c2354, c70, c2028, c38, c34, c319] c2355 unsat2355 (by rfl) a
  have h0 : Entails.eval a c2354 := derived2354 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c2028 := derived2028 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2356 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2354, some c70, some c2355, some c279, some c2273, some c34, some c2027, some c319, some c317, some c58, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2356 : lratChecker f2356 p2356 = .success := by decide +kernel
theorem unsat2356 : Unsatisfiable (PosFin 57) f2356 := by
  apply lratCheckerSound f2356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2356
  · intro a ha; simp [p2356] at ha; subst a; trivial
  · exact checked2356
theorem derived2356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2356 := by
  apply localUnsat_implies_entails f2356 [c2354, c70, c2355, c279, c2273, c34, c2027, c319, c317, c58] c2356 unsat2356 (by rfl) a
  have h0 : Entails.eval a c2354 := derived2354 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c2355 := derived2355 a h
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c2273 := derived2273 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2357 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2354, some c70, some c90, some c2356, some c66, some c2068, some c2097, some c314, some c58, some c38, some c333, some c274, some c34, some c2047, some c293, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2357 : lratChecker f2357 p2357 = .success := by decide +kernel
theorem unsat2357 : Unsatisfiable (PosFin 57) f2357 := by
  apply lratCheckerSound f2357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2357
  · intro a ha; simp [p2357] at ha; subst a; trivial
  · exact checked2357
theorem derived2357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2357 := by
  apply localUnsat_implies_entails f2357 [c2354, c70, c90, c2356, c66, c2068, c2097, c314, c58, c38, c333, c274, c34, c2047, c293] c2357 unsat2357 (by rfl) a
  have h0 : Entails.eval a c2354 := derived2354 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c2356 := derived2356 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c2097 := derived2097 a h
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c333 := h 332 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c2047 := derived2047 a h
  have h14 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2358 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨15, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2357, some c104, some c2041, some c365, some c2248, some c155, some c2008, some c295, some c335, some c38, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2358 : lratChecker f2358 p2358 = .success := by decide +kernel
theorem unsat2358 : Unsatisfiable (PosFin 57) f2358 := by
  apply lratCheckerSound f2358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2358
  · intro a ha; simp [p2358] at ha; subst a; trivial
  · exact checked2358
theorem derived2358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2358 := by
  apply localUnsat_implies_entails f2358 [c2201, c2357, c104, c2041, c365, c2248, c155, c2008, c295, c335, c38] c2358 unsat2358 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2357 := derived2357 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2041 := derived2041 a h
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c2248 := derived2248 a h
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c2008 := derived2008 a h
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c335 := h 334 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2359 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨54, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2203, some c2357, some c104, some c82, some c69, some c369, some c2351, some c361, some c2066, some c377, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2359 : lratChecker f2359 p2359 = .success := by decide +kernel
theorem unsat2359 : Unsatisfiable (PosFin 57) f2359 := by
  apply lratCheckerSound f2359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2359
  · intro a ha; simp [p2359] at ha; subst a; trivial
  · exact checked2359
theorem derived2359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2359 := by
  apply localUnsat_implies_entails f2359 [c2201, c2203, c2357, c104, c82, c69, c369, c2351, c361, c2066, c377] c2359 unsat2359 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2203 := derived2203 a h
  have h2 : Entails.eval a c2357 := derived2357 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c2351 := derived2351 a h
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c2066 := derived2066 a h
  have h10 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2360 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2357, some c104, some c2353, some c2203, some c1051, some c2359, some c2358, some c2035, some c2350, some c2351, some c1085, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2360 : lratChecker f2360 p2360 = .success := by decide +kernel
theorem unsat2360 : Unsatisfiable (PosFin 57) f2360 := by
  apply lratCheckerSound f2360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2360
  · intro a ha; simp [p2360] at ha; subst a; trivial
  · exact checked2360
theorem derived2360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2360 := by
  apply localUnsat_implies_entails f2360 [c2201, c2345, c2357, c104, c2353, c2203, c1051, c2359, c2358, c2035, c2350, c2351, c1085] c2360 unsat2360 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2357 := derived2357 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2353 := derived2353 a h
  have h5 : Entails.eval a c2203 := derived2203 a h
  have h6 : Entails.eval a c1051 := derived1051 a h
  have h7 : Entails.eval a c2359 := derived2359 a h
  have h8 : Entails.eval a c2358 := derived2358 a h
  have h9 : Entails.eval a c2035 := derived2035 a h
  have h10 : Entails.eval a c2350 := derived2350 a h
  have h11 : Entails.eval a c2351 := derived2351 a h
  have h12 : Entails.eval a c1085 := derived1085 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2361 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2273, some c38, some c319, some c314, some c2050, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2361 : lratChecker f2361 p2361 = .success := by decide +kernel
theorem unsat2361 : Unsatisfiable (PosFin 57) f2361 := by
  apply lratCheckerSound f2361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2361
  · intro a ha; simp [p2361] at ha; subst a; trivial
  · exact checked2361
theorem derived2361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2361 := by
  apply localUnsat_implies_entails f2361 [c2273, c38, c319, c314, c2050] c2361 unsat2361 (by rfl) a
  have h0 : Entails.eval a c2273 := derived2273 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c2050 := derived2050 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2362 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2357, some c104, some c2360, some c70, some c94, some c1055, some c2361, some c2035, some c2265, some c289, some c319, some c2025, some c62, some c329, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2362 : lratChecker f2362 p2362 = .success := by decide +kernel
theorem unsat2362 : Unsatisfiable (PosFin 57) f2362 := by
  apply lratCheckerSound f2362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2362
  · intro a ha; simp [p2362] at ha; subst a; trivial
  · exact checked2362
theorem derived2362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2362 := by
  apply localUnsat_implies_entails f2362 [c2201, c2345, c2357, c104, c2360, c70, c94, c1055, c2361, c2035, c2265, c289, c319, c2025, c62, c329] c2362 unsat2362 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2357 := derived2357 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2360 := derived2360 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c1055 := derived1055 a h
  have h8 : Entails.eval a c2361 := derived2361 a h
  have h9 : Entails.eval a c2035 := derived2035 a h
  have h10 : Entails.eval a c2265 := derived2265 a h
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c2025 := derived2025 a h
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2363 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2203, some c2358, some c1051, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2363 : lratChecker f2363 p2363 = .success := by decide +kernel
theorem unsat2363 : Unsatisfiable (PosFin 57) f2363 := by
  apply lratCheckerSound f2363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2363
  · intro a ha; simp [p2363] at ha; subst a; trivial
  · exact checked2363
theorem derived2363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2363 := by
  apply localUnsat_implies_entails f2363 [c2201, c2203, c2358, c1051] c2363 unsat2363 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2203 := derived2203 a h
  have h2 : Entails.eval a c2358 := derived2358 a h
  have h3 : Entails.eval a c1051 := derived1051 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2364 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2353, some c2357, some c104, some c2362, some c2068, some c76, some c2312, some c2363, some c70, some c2251, some c976, some c2285, some c361, some c360, some c841, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2364 : lratChecker f2364 p2364 = .success := by decide +kernel
theorem unsat2364 : Unsatisfiable (PosFin 57) f2364 := by
  apply lratCheckerSound f2364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2364
  · intro a ha; simp [p2364] at ha; subst a; trivial
  · exact checked2364
theorem derived2364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2364 := by
  apply localUnsat_implies_entails f2364 [c2201, c2345, c2353, c2357, c104, c2362, c2068, c76, c2312, c2363, c70, c2251, c976, c2285, c361, c360, c841] c2364 unsat2364 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2353 := derived2353 a h
  have h3 : Entails.eval a c2357 := derived2357 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2362 := derived2362 a h
  have h6 : Entails.eval a c2068 := derived2068 a h
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c2312 := derived2312 a h
  have h9 : Entails.eval a c2363 := derived2363 a h
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c2251 := derived2251 a h
  have h12 : Entails.eval a c976 := derived976 a h
  have h13 : Entails.eval a c2285 := derived2285 a h
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2365 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨47, by decide⟩, true), (⟨44, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2230, some c379, some c360, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2365 : lratChecker f2365 p2365 = .success := by decide +kernel
theorem unsat2365 : Unsatisfiable (PosFin 57) f2365 := by
  apply lratCheckerSound f2365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2365
  · intro a ha; simp [p2365] at ha; subst a; trivial
  · exact checked2365
theorem derived2365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2365 := by
  apply localUnsat_implies_entails f2365 [c2230, c379, c360] c2365 unsat2365 (by rfl) a
  have h0 : Entails.eval a c2230 := derived2230 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2366 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨34, by decide⟩, true), (⟨36, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2049, some c297, some c190, some c192, some c22, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2366 : lratChecker f2366 p2366 = .success := by decide +kernel
theorem unsat2366 : Unsatisfiable (PosFin 57) f2366 := by
  apply lratCheckerSound f2366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2366
  · intro a ha; simp [p2366] at ha; subst a; trivial
  · exact checked2366
theorem derived2366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2366 := by
  apply localUnsat_implies_entails f2366 [c2364, c100, c2345, c2049, c297, c190, c192, c22] c2366 unsat2366 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2049 := derived2049 a h
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2367 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨36, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2366, some c35, some c46, some c322, some c301, some c1655, some c192, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2367 : lratChecker f2367 p2367 = .success := by decide +kernel
theorem unsat2367 : Unsatisfiable (PosFin 57) f2367 := by
  apply lratCheckerSound f2367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2367
  · intro a ha; simp [p2367] at ha; subst a; trivial
  · exact checked2367
theorem derived2367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2367 := by
  apply localUnsat_implies_entails f2367 [c2364, c100, c2345, c2366, c35, c46, c322, c301, c1655, c192] c2367 unsat2367 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2366 := derived2366 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c1655 := derived1655 a h
  have h9 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2368 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2367, some c317, some c2026, some c35, some c313, some c282, some c297, some c193, some c192, some c28, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2368 : lratChecker f2368 p2368 = .success := by decide +kernel
theorem unsat2368 : Unsatisfiable (PosFin 57) f2368 := by
  apply lratCheckerSound f2368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2368
  · intro a ha; simp [p2368] at ha; subst a; trivial
  · exact checked2368
theorem derived2368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2368 := by
  apply localUnsat_implies_entails f2368 [c2364, c100, c2367, c317, c2026, c35, c313, c282, c297, c193, c192, c28] c2368 unsat2368 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2367 := derived2367 a h
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c2026 := derived2026 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2369 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c2345, some c2364, some c100, some c2151, some c172, some c6, some c152, some c2368, some c341, some c337, some c58, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2369 : lratChecker f2369 p2369 = .success := by decide +kernel
theorem unsat2369 : Unsatisfiable (PosFin 57) f2369 := by
  apply lratCheckerSound f2369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2369
  · intro a ha; simp [p2369] at ha; subst a; trivial
  · exact checked2369
theorem derived2369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2369 := by
  apply localUnsat_implies_entails f2369 [c153, c2345, c2364, c100, c2151, c172, c6, c152, c2368, c341, c337, c58] c2369 unsat2369 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2151 := derived2151 a h
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c2368 := derived2368 a h
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c337 := h 336 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2370 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨45, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c282, some c1014, some c264, some c2026, some c313, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2370 : lratChecker f2370 p2370 = .success := by decide +kernel
theorem unsat2370 : Unsatisfiable (PosFin 57) f2370 := by
  apply lratCheckerSound f2370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2370
  · intro a ha; simp [p2370] at ha; subst a; trivial
  · exact checked2370
theorem derived2370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2370 := by
  apply localUnsat_implies_entails f2370 [c293, c282, c1014, c264, c2026, c313] c2370 unsat2370 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c1014 := derived1014 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c2026 := derived2026 a h
  have h5 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2371 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2151, some c367, some c2365, some c370, some c78, some c2260, some c153, some c2369, some c1688, some c2370, some c2047, some c35, some c46, some c273, some c322, some c295, some c264, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2371 : lratChecker f2371 p2371 = .success := by decide +kernel
theorem unsat2371 : Unsatisfiable (PosFin 57) f2371 := by
  apply lratCheckerSound f2371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2371
  · intro a ha; simp [p2371] at ha; subst a; trivial
  · exact checked2371
theorem derived2371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2371 := by
  apply localUnsat_implies_entails f2371 [c2364, c100, c2345, c2151, c367, c2365, c370, c78, c2260, c153, c2369, c1688, c2370, c2047, c35, c46, c273, c322, c295, c264] c2371 unsat2371 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2365 := derived2365 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c2260 := derived2260 a h
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c2369 := derived2369 a h
  have h11 : Entails.eval a c1688 := derived1688 a h
  have h12 : Entails.eval a c2370 := derived2370 a h
  have h13 : Entails.eval a c2047 := derived2047 a h
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c273 := h 272 (by decide)
  have h17 : Entails.eval a c322 := h 321 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  have h19 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2372 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨5, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c172, some c169, some c2020, some c181, some c168, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2372 : lratChecker f2372 p2372 = .success := by decide +kernel
theorem unsat2372 : Unsatisfiable (PosFin 57) f2372 := by
  apply lratCheckerSound f2372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2372
  · intro a ha; simp [p2372] at ha; subst a; trivial
  · exact checked2372
theorem derived2372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2372 := by
  apply localUnsat_implies_entails f2372 [c172, c169, c2020, c181, c168] c2372 unsat2372 (by rfl) a
  have h0 : Entails.eval a c172 := h 171 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c2020 := derived2020 a h
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2373 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2047, some c35, some c273, some c322, some c37, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2373 : lratChecker f2373 p2373 = .success := by decide +kernel
theorem unsat2373 : Unsatisfiable (PosFin 57) f2373 := by
  apply lratCheckerSound f2373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2373
  · intro a ha; simp [p2373] at ha; subst a; trivial
  · exact checked2373
theorem derived2373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2373 := by
  apply localUnsat_implies_entails f2373 [c2047, c35, c273, c322, c37] c2373 unsat2373 (by rfl) a
  have h0 : Entails.eval a c2047 := derived2047 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2374 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c370, some c78, some c367, some c2151, some c2365, some c2371, some c69, some c2373, some c282, some c1014, some c37, some c2026, some c313, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2374 : lratChecker f2374 p2374 = .success := by decide +kernel
theorem unsat2374 : Unsatisfiable (PosFin 57) f2374 := by
  apply lratCheckerSound f2374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2374
  · intro a ha; simp [p2374] at ha; subst a; trivial
  · exact checked2374
theorem derived2374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2374 := by
  apply localUnsat_implies_entails f2374 [c2364, c100, c2345, c370, c78, c367, c2151, c2365, c2371, c69, c2373, c282, c1014, c37, c2026, c313] c2374 unsat2374 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c2151 := derived2151 a h
  have h7 : Entails.eval a c2365 := derived2365 a h
  have h8 : Entails.eval a c2371 := derived2371 a h
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c2373 := derived2373 a h
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c1014 := derived1014 a h
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c2026 := derived2026 a h
  have h15 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2375 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2364, some c100, some c2151, some c370, some c367, some c78, some c2374, some c1118, some c2036, some c1491, some c2048, some c2045, some c2021, some c277, some c317, some c153, some c2230, some c155, some c143, some c127, some c265, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2375 : lratChecker f2375 p2375 = .success := by decide +kernel
theorem unsat2375 : Unsatisfiable (PosFin 57) f2375 := by
  apply lratCheckerSound f2375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2375
  · intro a ha; simp [p2375] at ha; subst a; trivial
  · exact checked2375
theorem derived2375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2375 := by
  apply localUnsat_implies_entails f2375 [c2345, c2364, c100, c2151, c370, c367, c78, c2374, c1118, c2036, c1491, c2048, c2045, c2021, c277, c317, c153, c2230, c155, c143, c127, c265] c2375 unsat2375 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c2374 := derived2374 a h
  have h8 : Entails.eval a c1118 := derived1118 a h
  have h9 : Entails.eval a c2036 := derived2036 a h
  have h10 : Entails.eval a c1491 := derived1491 a h
  have h11 : Entails.eval a c2048 := derived2048 a h
  have h12 : Entails.eval a c2045 := derived2045 a h
  have h13 : Entails.eval a c2021 := derived2021 a h
  have h14 : Entails.eval a c277 := h 276 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c2230 := derived2230 a h
  have h18 : Entails.eval a c155 := h 154 (by decide)
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c127 := h 126 (by decide)
  have h21 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2376 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c377, some c361, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2376 : lratChecker f2376 p2376 = .success := by decide +kernel
theorem unsat2376 : Unsatisfiable (PosFin 57) f2376 := by
  apply lratCheckerSound f2376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2376
  · intro a ha; simp [p2376] at ha; subst a; trivial
  · exact checked2376
theorem derived2376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2376 := by
  apply localUnsat_implies_entails f2376 [c378, c377, c361] c2376 unsat2376 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2377 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2364, some c100, some c2151, some c2375, some c2376, some c2365, some c2260, some c2369, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2377 : lratChecker f2377 p2377 = .success := by decide +kernel
theorem unsat2377 : Unsatisfiable (PosFin 57) f2377 := by
  apply lratCheckerSound f2377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2377
  · intro a ha; simp [p2377] at ha; subst a; trivial
  · exact checked2377
theorem derived2377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2377 := by
  apply localUnsat_implies_entails f2377 [c2345, c2364, c100, c2151, c2375, c2376, c2365, c2260, c2369] c2377 unsat2377 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c2375 := derived2375 a h
  have h5 : Entails.eval a c2376 := derived2376 a h
  have h6 : Entails.eval a c2365 := derived2365 a h
  have h7 : Entails.eval a c2260 := derived2260 a h
  have h8 : Entails.eval a c2369 := derived2369 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2378 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨34, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c341, some c343, some c2366, some c40, some c2047, some c46, some c306, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2378 : lratChecker f2378 p2378 = .success := by decide +kernel
theorem unsat2378 : Unsatisfiable (PosFin 57) f2378 := by
  apply lratCheckerSound f2378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2378
  · intro a ha; simp [p2378] at ha; subst a; trivial
  · exact checked2378
theorem derived2378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2378 := by
  apply localUnsat_implies_entails f2378 [c2364, c100, c2345, c341, c343, c2366, c40, c2047, c46, c306] c2378 unsat2378 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c2366 := derived2366 a h
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c2047 := derived2047 a h
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2379 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2378, some c58, some c38, some c337, some c303, some c2366, some c47, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2379 : lratChecker f2379 p2379 = .success := by decide +kernel
theorem unsat2379 : Unsatisfiable (PosFin 57) f2379 := by
  apply lratCheckerSound f2379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2379
  · intro a ha; simp [p2379] at ha; subst a; trivial
  · exact checked2379
theorem derived2379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2379 := by
  apply localUnsat_implies_entails f2379 [c2364, c100, c2345, c2378, c58, c38, c337, c303, c2366, c47] c2379 unsat2379 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2378 := derived2378 a h
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c337 := h 336 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c2366 := derived2366 a h
  have h9 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2380 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, false), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c100, some c2094, some c2345, some c2151, some c2376, some c153, some c2171, some c363, some c12, some c14, some c2296, some c165, some c173, some c2379, some c317, some c140, some c59, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2380 : lratChecker f2380 p2380 = .success := by decide +kernel
theorem unsat2380 : Unsatisfiable (PosFin 57) f2380 := by
  apply lratCheckerSound f2380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2380
  · intro a ha; simp [p2380] at ha; subst a; trivial
  · exact checked2380
theorem derived2380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2380 := by
  apply localUnsat_implies_entails f2380 [c2201, c2364, c100, c2094, c2345, c2151, c2376, c153, c2171, c363, c12, c14, c2296, c165, c173, c2379, c317, c140, c59] c2380 unsat2380 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c2345 := derived2345 a h
  have h5 : Entails.eval a c2151 := derived2151 a h
  have h6 : Entails.eval a c2376 := derived2376 a h
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c2171 := derived2171 a h
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c2296 := derived2296 a h
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c2379 := derived2379 a h
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2380

end CochromaticTwenty.Certificates.B16_8_2
