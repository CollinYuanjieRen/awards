import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1700_1799

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2214 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2214 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c158, some c2117, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2214 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2214 : lratChecker f2214 p2214 = .success := by decide +kernel
theorem unsat2214 : Unsatisfiable (PosFin 57) f2214 := by
  apply lratCheckerSound f2214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2214
  · intro a ha; simp [p2214] at ha; subst a; trivial
  · exact checked2214
theorem derived2214 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2214 := by
  apply localUnsat_implies_entails f2214 [c160, c158, c2117] c2214 unsat2214 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c2117 := derived2117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2215 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2215 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2209, some c2207, some c128, some c119, some c7, some c2173, some c2192, some c56, some c2091, some c2116, some c2212, some c2213, some c2214, some c58, some c2084, some c2122, some c188, some c156, some c59, some c2106, some c2117, some c352, some c2118, some c344, some c245, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2215 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2215 : lratChecker f2215 p2215 = .success := by decide +kernel
theorem unsat2215 : Unsatisfiable (PosFin 57) f2215 := by
  apply lratCheckerSound f2215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2215
  · intro a ha; simp [p2215] at ha; subst a; trivial
  · exact checked2215
theorem derived2215 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2215 := by
  apply localUnsat_implies_entails f2215 [c2209, c2207, c128, c119, c7, c2173, c2192, c56, c2091, c2116, c2212, c2213, c2214, c58, c2084, c2122, c188, c156, c59, c2106, c2117, c352, c2118, c344, c245] c2215 unsat2215 (by rfl) a
  have h0 : Entails.eval a c2209 := derived2209 a h
  have h1 : Entails.eval a c2207 := derived2207 a h
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c2173 := derived2173 a h
  have h6 : Entails.eval a c2192 := derived2192 a h
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c2091 := derived2091 a h
  have h9 : Entails.eval a c2116 := derived2116 a h
  have h10 : Entails.eval a c2212 := derived2212 a h
  have h11 : Entails.eval a c2213 := derived2213 a h
  have h12 : Entails.eval a c2214 := derived2214 a h
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c2084 := derived2084 a h
  have h15 : Entails.eval a c2122 := derived2122 a h
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c59 := h 58 (by decide)
  have h19 : Entails.eval a c2106 := derived2106 a h
  have h20 : Entails.eval a c2117 := derived2117 a h
  have h21 : Entails.eval a c352 := h 351 (by decide)
  have h22 : Entails.eval a c2118 := derived2118 a h
  have h23 : Entails.eval a c344 := h 343 (by decide)
  have h24 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2216 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2216 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2209, some c2207, some c128, some c119, some c7, some c2173, some c2094, some c200, some c2215, some c2126, some c2129, some c1024, some c51, some c146, some c2154, some c142, some c58, some c2084, some c68, some c271, some c2122, some c2135, some c270, some c224, some c339, some c352, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2216 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2216 : lratChecker f2216 p2216 = .success := by decide +kernel
theorem unsat2216 : Unsatisfiable (PosFin 57) f2216 := by
  apply lratCheckerSound f2216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2216
  · intro a ha; simp [p2216] at ha; subst a; trivial
  · exact checked2216
theorem derived2216 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2216 := by
  apply localUnsat_implies_entails f2216 [c2085, c2209, c2207, c128, c119, c7, c2173, c2094, c200, c2215, c2126, c2129, c1024, c51, c146, c2154, c142, c58, c2084, c68, c271, c2122, c2135, c270, c224, c339, c352] c2216 unsat2216 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2209 := derived2209 a h
  have h2 : Entails.eval a c2207 := derived2207 a h
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c2173 := derived2173 a h
  have h7 : Entails.eval a c2094 := derived2094 a h
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c2215 := derived2215 a h
  have h10 : Entails.eval a c2126 := derived2126 a h
  have h11 : Entails.eval a c2129 := derived2129 a h
  have h12 : Entails.eval a c1024 := derived1024 a h
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c2154 := derived2154 a h
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c2084 := derived2084 a h
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c271 := h 270 (by decide)
  have h21 : Entails.eval a c2122 := derived2122 a h
  have h22 : Entails.eval a c2135 := derived2135 a h
  have h23 : Entails.eval a c270 := h 269 (by decide)
  have h24 : Entails.eval a c224 := h 223 (by decide)
  have h25 : Entails.eval a c339 := h 338 (by decide)
  have h26 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2217 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2217 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2207, some c119, some c7, some c2173, some c2085, some c2209, some c2216, some c819, some c2124, some c56, some c2136, some c2093, some c2110, some c1952, some c156, some c284, some c2081, some c2084, some c224, some c246, some c349, some c345, some c2082, some c339, some c374, some c1024, some c2122, some c96, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2217 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2217 : lratChecker f2217 p2217 = .success := by decide +kernel
theorem unsat2217 : Unsatisfiable (PosFin 57) f2217 := by
  apply lratCheckerSound f2217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2217
  · intro a ha; simp [p2217] at ha; subst a; trivial
  · exact checked2217
theorem derived2217 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2217 := by
  apply localUnsat_implies_entails f2217 [c2207, c119, c7, c2173, c2085, c2209, c2216, c819, c2124, c56, c2136, c2093, c2110, c1952, c156, c284, c2081, c2084, c224, c246, c349, c345, c2082, c339, c374, c1024, c2122, c96] c2217 unsat2217 (by rfl) a
  have h0 : Entails.eval a c2207 := derived2207 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c2173 := derived2173 a h
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2209 := derived2209 a h
  have h6 : Entails.eval a c2216 := derived2216 a h
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c2124 := derived2124 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c2136 := derived2136 a h
  have h11 : Entails.eval a c2093 := derived2093 a h
  have h12 : Entails.eval a c2110 := derived2110 a h
  have h13 : Entails.eval a c1952 := derived1952 a h
  have h14 : Entails.eval a c156 := h 155 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c2081 := derived2081 a h
  have h17 : Entails.eval a c2084 := derived2084 a h
  have h18 : Entails.eval a c224 := h 223 (by decide)
  have h19 : Entails.eval a c246 := h 245 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  have h21 : Entails.eval a c345 := h 344 (by decide)
  have h22 : Entails.eval a c2082 := derived2082 a h
  have h23 : Entails.eval a c339 := h 338 (by decide)
  have h24 : Entails.eval a c374 := h 373 (by decide)
  have h25 : Entails.eval a c1024 := derived1024 a h
  have h26 : Entails.eval a c2122 := derived2122 a h
  have h27 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2218 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2218 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2207, some c119, some c7, some c2091, some c2093, some c56, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2218 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2218 : lratChecker f2218 p2218 = .success := by decide +kernel
theorem unsat2218 : Unsatisfiable (PosFin 57) f2218 := by
  apply lratCheckerSound f2218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2218
  · intro a ha; simp [p2218] at ha; subst a; trivial
  · exact checked2218
theorem derived2218 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2218 := by
  apply localUnsat_implies_entails f2218 [c2207, c119, c7, c2091, c2093, c56] c2218 unsat2218 (by rfl) a
  have h0 : Entails.eval a c2207 := derived2207 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c2091 := derived2091 a h
  have h4 : Entails.eval a c2093 := derived2093 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2219 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2219 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c2217, some c1147, some c2218, some c202, some c198, some c2124, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2219 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2219 : lratChecker f2219 p2219 = .success := by decide +kernel
theorem unsat2219 : Unsatisfiable (PosFin 57) f2219 := by
  apply lratCheckerSound f2219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2219
  · intro a ha; simp [p2219] at ha; subst a; trivial
  · exact checked2219
theorem derived2219 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2219 := by
  apply localUnsat_implies_entails f2219 [c2173, c2217, c1147, c2218, c202, c198, c2124] c2219 unsat2219 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c2217 := derived2217 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c2218 := derived2218 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c198 := h 197 (by decide)
  have h6 : Entails.eval a c2124 := derived2124 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2220 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2220 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2138, some c108, some c2115, some c4, some c24, some c261, some c200, some c2090, some c115, some c1192, some c164, some c2118, some c168, some c63, some c76, some c247, some c347, some c2081, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2220 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2220 : lratChecker f2220 p2220 = .success := by decide +kernel
theorem unsat2220 : Unsatisfiable (PosFin 57) f2220 := by
  apply lratCheckerSound f2220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2220
  · intro a ha; simp [p2220] at ha; subst a; trivial
  · exact checked2220
theorem derived2220 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2220 := by
  apply localUnsat_implies_entails f2220 [c2219, c2138, c108, c2115, c4, c24, c261, c200, c2090, c115, c1192, c164, c2118, c168, c63, c76, c247, c347, c2081] c2220 unsat2220 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2138 := derived2138 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c2115 := derived2115 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c2090 := derived2090 a h
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c1192 := derived1192 a h
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c2118 := derived2118 a h
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c63 := h 62 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c247 := h 246 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  have h18 : Entails.eval a c2081 := derived2081 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2221 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2221 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2138, some c2220, some c1931, some c1967, some c1875, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2221 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2221 : lratChecker f2221 p2221 = .success := by decide +kernel
theorem unsat2221 : Unsatisfiable (PosFin 57) f2221 := by
  apply lratCheckerSound f2221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2221
  · intro a ha; simp [p2221] at ha; subst a; trivial
  · exact checked2221
theorem derived2221 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2221 := by
  apply localUnsat_implies_entails f2221 [c2219, c2138, c2220, c1931, c1967, c1875] c2221 unsat2221 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2138 := derived2138 a h
  have h2 : Entails.eval a c2220 := derived2220 a h
  have h3 : Entails.eval a c1931 := derived1931 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c1875 := derived1875 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2222 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2222 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c197, some c199, some c2148, some c2090, some c200, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2222 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2222 : lratChecker f2222 p2222 = .success := by decide +kernel
theorem unsat2222 : Unsatisfiable (PosFin 57) f2222 := by
  apply lratCheckerSound f2222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2222
  · intro a ha; simp [p2222] at ha; subst a; trivial
  · exact checked2222
theorem derived2222 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2222 := by
  apply localUnsat_implies_entails f2222 [c2219, c197, c199, c2148, c2090, c200] c2222 unsat2222 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c2148 := derived2148 a h
  have h4 : Entails.eval a c2090 := derived2090 a h
  have h5 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2223 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2223 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2094, some c2222, some c2126, some c200, some c2214, some c115, some c2084, some c69, some c2147, some c346, some c25, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2223 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2223 : lratChecker f2223 p2223 = .success := by decide +kernel
theorem unsat2223 : Unsatisfiable (PosFin 57) f2223 := by
  apply lratCheckerSound f2223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2223
  · intro a ha; simp [p2223] at ha; subst a; trivial
  · exact checked2223
theorem derived2223 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2223 := by
  apply localUnsat_implies_entails f2223 [c2219, c2094, c2222, c2126, c200, c2214, c115, c2084, c69, c2147, c346, c25] c2223 unsat2223 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2222 := derived2222 a h
  have h3 : Entails.eval a c2126 := derived2126 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c2214 := derived2214 a h
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c2084 := derived2084 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c2147 := derived2147 a h
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2224 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2224 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2094, some c2222, some c2223, some c4, some c2148, some c2114, some c111, some c2149, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2224 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2224 : lratChecker f2224 p2224 = .success := by decide +kernel
theorem unsat2224 : Unsatisfiable (PosFin 57) f2224 := by
  apply lratCheckerSound f2224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2224
  · intro a ha; simp [p2224] at ha; subst a; trivial
  · exact checked2224
theorem derived2224 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2224 := by
  apply localUnsat_implies_entails f2224 [c2219, c2085, c2094, c2222, c2223, c4, c2148, c2114, c111, c2149] c2224 unsat2224 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2222 := derived2222 a h
  have h4 : Entails.eval a c2223 := derived2223 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c2148 := derived2148 a h
  have h7 : Entails.eval a c2114 := derived2114 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c2149 := derived2149 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2225 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2225 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2146, some c2090, some c200, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2225 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2225 : lratChecker f2225 p2225 = .success := by decide +kernel
theorem unsat2225 : Unsatisfiable (PosFin 57) f2225 := by
  apply lratCheckerSound f2225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2225
  · intro a ha; simp [p2225] at ha; subst a; trivial
  · exact checked2225
theorem derived2225 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2225 := by
  apply localUnsat_implies_entails f2225 [c2146, c2090, c200] c2225 unsat2225 (by rfl) a
  have h0 : Entails.eval a c2146 := derived2146 a h
  have h1 : Entails.eval a c2090 := derived2090 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2226 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2226 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2225, some c199, some c2126, some c2085, some c2221, some c261, some c2224, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2226 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2226 : lratChecker f2226 p2226 = .success := by decide +kernel
theorem unsat2226 : Unsatisfiable (PosFin 57) f2226 := by
  apply lratCheckerSound f2226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2226
  · intro a ha; simp [p2226] at ha; subst a; trivial
  · exact checked2226
theorem derived2226 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2226 := by
  apply localUnsat_implies_entails f2226 [c2219, c2225, c199, c2126, c2085, c2221, c261, c2224] c2226 unsat2226 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2225 := derived2225 a h
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c2126 := derived2126 a h
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2221 := derived2221 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c2224 := derived2224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2227 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2227 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2225, some c2085, some c2226, some c27, some c36, some c1024, some c168, some c108, some c2137, some c2117, some c352, some c349, some c68, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2227 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2227 : lratChecker f2227 p2227 = .success := by decide +kernel
theorem unsat2227 : Unsatisfiable (PosFin 57) f2227 := by
  apply lratCheckerSound f2227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2227
  · intro a ha; simp [p2227] at ha; subst a; trivial
  · exact checked2227
theorem derived2227 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2227 := by
  apply localUnsat_implies_entails f2227 [c2219, c2225, c2085, c2226, c27, c36, c1024, c168, c108, c2137, c2117, c352, c349, c68] c2227 unsat2227 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2225 := derived2225 a h
  have h2 : Entails.eval a c2085 := derived2085 a h
  have h3 : Entails.eval a c2226 := derived2226 a h
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c1024 := derived1024 a h
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c2137 := derived2137 a h
  have h10 : Entails.eval a c2117 := derived2117 a h
  have h11 : Entails.eval a c352 := h 351 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2228 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2228 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2225, some c199, some c2085, some c2227, some c3, some c1876, some c200, some c4, some c2114, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2228 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2228 : lratChecker f2228 p2228 = .success := by decide +kernel
theorem unsat2228 : Unsatisfiable (PosFin 57) f2228 := by
  apply lratCheckerSound f2228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2228
  · intro a ha; simp [p2228] at ha; subst a; trivial
  · exact checked2228
theorem derived2228 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2228 := by
  apply localUnsat_implies_entails f2228 [c2219, c2225, c199, c2085, c2227, c3, c1876, c200, c4, c2114] c2228 unsat2228 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2225 := derived2225 a h
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2227 := derived2227 a h
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1876 := derived1876 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c2114 := derived2114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2229 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2229 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1974, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p2229 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2229 : lratChecker f2229 p2229 = .success := by decide +kernel
theorem unsat2229 : Unsatisfiable (PosFin 57) f2229 := by
  apply lratCheckerSound f2229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2229
  · intro a ha; simp [p2229] at ha; subst a; trivial
  · exact checked2229
theorem derived2229 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2229 := by
  apply localUnsat_implies_entails f2229 [c108, c1974] c2229 unsat2229 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1974 := derived1974 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2230 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨37, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2230 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c199, some c2126, some c2085, some c2214, some c164, some c58, some c2084, some c24, some c2117, some c2135, some c49, some c2110, some c272, some c62, some c133, some c55, some c230, some c899, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2230 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2230 : lratChecker f2230 p2230 = .success := by decide +kernel
theorem unsat2230 : Unsatisfiable (PosFin 57) f2230 := by
  apply lratCheckerSound f2230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2230
  · intro a ha; simp [p2230] at ha; subst a; trivial
  · exact checked2230
theorem derived2230 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2230 := by
  apply localUnsat_implies_entails f2230 [c2219, c199, c2126, c2085, c2214, c164, c58, c2084, c24, c2117, c2135, c49, c2110, c272, c62, c133, c55, c230, c899] c2230 unsat2230 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c2126 := derived2126 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2214 := derived2214 a h
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c2084 := derived2084 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c2117 := derived2117 a h
  have h10 : Entails.eval a c2135 := derived2135 a h
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c2110 := derived2110 a h
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c55 := h 54 (by decide)
  have h17 : Entails.eval a c230 := h 229 (by decide)
  have h18 : Entails.eval a c899 := derived899 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2231 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2231 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2228, some c112, some c2225, some c199, some c2126, some c2085, some c261, some c2174, some c1723, some c5, some c25, some c56, some c204, some c115, some c2229, some c2230, some c4, some c116, some c49, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2231 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2231 : lratChecker f2231 p2231 = .success := by decide +kernel
theorem unsat2231 : Unsatisfiable (PosFin 57) f2231 := by
  apply lratCheckerSound f2231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2231
  · intro a ha; simp [p2231] at ha; subst a; trivial
  · exact checked2231
theorem derived2231 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2231 := by
  apply localUnsat_implies_entails f2231 [c2219, c2228, c112, c2225, c199, c2126, c2085, c261, c2174, c1723, c5, c25, c56, c204, c115, c2229, c2230, c4, c116, c49] c2231 unsat2231 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2228 := derived2228 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c2225 := derived2225 a h
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c2126 := derived2126 a h
  have h6 : Entails.eval a c2085 := derived2085 a h
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c2174 := derived2174 a h
  have h9 : Entails.eval a c1723 := derived1723 a h
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c115 := h 114 (by decide)
  have h15 : Entails.eval a c2229 := derived2229 a h
  have h16 : Entails.eval a c2230 := derived2230 a h
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c116 := h 115 (by decide)
  have h19 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2232 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2232 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2138, some c108, some c18, some c4, some c24, some c1909, some c2111, some c245, some c192, some c2127, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2232 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2232 : lratChecker f2232 p2232 = .success := by decide +kernel
theorem unsat2232 : Unsatisfiable (PosFin 57) f2232 := by
  apply lratCheckerSound f2232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2232
  · intro a ha; simp [p2232] at ha; subst a; trivial
  · exact checked2232
theorem derived2232 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2232 := by
  apply localUnsat_implies_entails f2232 [c2219, c2138, c108, c18, c4, c24, c1909, c2111, c245, c192, c2127] c2232 unsat2232 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2138 := derived2138 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1909 := derived1909 a h
  have h7 : Entails.eval a c2111 := derived2111 a h
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c2127 := derived2127 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2233 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2233 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2094, some c2225, some c199, some c2126, some c2228, some c112, some c2231, some c2232, some c200, some c2214, some c115, some c68, some c58, some c2084, some c1783, some c51, some c1021, some c2135, some c188, some c186, some c346, some c2143, some c24, some c886, some c212, some c18, some c2127, some c352, some c280, some c315, some c245, some c2137, some c1881, some c150, some c137, some c2110, some c55, some c229, some c330, some c345, some c170, some c133, some c362, some c87, some c91, some c289, some c2112, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2233 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]]
theorem checked2233 : lratChecker f2233 p2233 = .success := by decide +kernel
theorem unsat2233 : Unsatisfiable (PosFin 57) f2233 := by
  apply lratCheckerSound f2233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2233
  · intro a ha; simp [p2233] at ha; subst a; trivial
  · exact checked2233
theorem derived2233 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2233 := by
  apply localUnsat_implies_entails f2233 [c2219, c2085, c2094, c2225, c199, c2126, c2228, c112, c2231, c2232, c200, c2214, c115, c68, c58, c2084, c1783, c51, c1021, c2135, c188, c186, c346, c2143, c24, c886, c212, c18, c2127, c352, c280, c315, c245, c2137, c1881, c150, c137, c2110, c55, c229, c330, c345, c170, c133, c362, c87, c91, c289, c2112] c2233 unsat2233 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2225 := derived2225 a h
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c2126 := derived2126 a h
  have h6 : Entails.eval a c2228 := derived2228 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c2231 := derived2231 a h
  have h9 : Entails.eval a c2232 := derived2232 a h
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c2214 := derived2214 a h
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c2084 := derived2084 a h
  have h16 : Entails.eval a c1783 := derived1783 a h
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c1021 := derived1021 a h
  have h19 : Entails.eval a c2135 := derived2135 a h
  have h20 : Entails.eval a c188 := h 187 (by decide)
  have h21 : Entails.eval a c186 := h 185 (by decide)
  have h22 : Entails.eval a c346 := h 345 (by decide)
  have h23 : Entails.eval a c2143 := derived2143 a h
  have h24 : Entails.eval a c24 := h 23 (by decide)
  have h25 : Entails.eval a c886 := derived886 a h
  have h26 : Entails.eval a c212 := h 211 (by decide)
  have h27 : Entails.eval a c18 := h 17 (by decide)
  have h28 : Entails.eval a c2127 := derived2127 a h
  have h29 : Entails.eval a c352 := h 351 (by decide)
  have h30 : Entails.eval a c280 := h 279 (by decide)
  have h31 : Entails.eval a c315 := h 314 (by decide)
  have h32 : Entails.eval a c245 := h 244 (by decide)
  have h33 : Entails.eval a c2137 := derived2137 a h
  have h34 : Entails.eval a c1881 := derived1881 a h
  have h35 : Entails.eval a c150 := h 149 (by decide)
  have h36 : Entails.eval a c137 := h 136 (by decide)
  have h37 : Entails.eval a c2110 := derived2110 a h
  have h38 : Entails.eval a c55 := h 54 (by decide)
  have h39 : Entails.eval a c229 := h 228 (by decide)
  have h40 : Entails.eval a c330 := h 329 (by decide)
  have h41 : Entails.eval a c345 := h 344 (by decide)
  have h42 : Entails.eval a c170 := h 169 (by decide)
  have h43 : Entails.eval a c133 := h 132 (by decide)
  have h44 : Entails.eval a c362 := h 361 (by decide)
  have h45 : Entails.eval a c87 := h 86 (by decide)
  have h46 : Entails.eval a c91 := h 90 (by decide)
  have h47 : Entails.eval a c289 := h 288 (by decide)
  have h48 : Entails.eval a c2112 := derived2112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2234 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2234 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2228, some c2085, some c2094, some c2231, some c2233, some c4, some c2148, some c1783, some c204, some c115, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2234 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2234 : lratChecker f2234 p2234 = .success := by decide +kernel
theorem unsat2234 : Unsatisfiable (PosFin 57) f2234 := by
  apply lratCheckerSound f2234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2234
  · intro a ha; simp [p2234] at ha; subst a; trivial
  · exact checked2234
theorem derived2234 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2234 := by
  apply localUnsat_implies_entails f2234 [c2219, c2228, c2085, c2094, c2231, c2233, c4, c2148, c1783, c204, c115] c2234 unsat2234 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2228 := derived2228 a h
  have h2 : Entails.eval a c2085 := derived2085 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c2231 := derived2231 a h
  have h5 : Entails.eval a c2233 := derived2233 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c2148 := derived2148 a h
  have h8 : Entails.eval a c1783 := derived1783 a h
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2235 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2235 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2094, some c2225, some c199, some c2126, some c2234, some c3, some c1967, some c200, some c4, some c116, some c2114, some c18, some c52, some c117, some c137, some c229, some c88, some c171, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2235 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2235 : lratChecker f2235 p2235 = .success := by decide +kernel
theorem unsat2235 : Unsatisfiable (PosFin 57) f2235 := by
  apply lratCheckerSound f2235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2235
  · intro a ha; simp [p2235] at ha; subst a; trivial
  · exact checked2235
theorem derived2235 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2235 := by
  apply localUnsat_implies_entails f2235 [c2219, c2085, c2094, c2225, c199, c2126, c2234, c3, c1967, c200, c4, c116, c2114, c18, c52, c117, c137, c229, c88, c171] c2235 unsat2235 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2225 := derived2225 a h
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c2126 := derived2126 a h
  have h6 : Entails.eval a c2234 := derived2234 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c1967 := derived1967 a h
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c2114 := derived2114 a h
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c137 := h 136 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c88 := h 87 (by decide)
  have h19 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2236 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2236 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c168, some c63, some c76, some c247, some c347, some c2081, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2236 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2236 : lratChecker f2236 p2236 = .success := by decide +kernel
theorem unsat2236 : Unsatisfiable (PosFin 57) f2236 := by
  apply lratCheckerSound f2236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2236
  · intro a ha; simp [p2236] at ha; subst a; trivial
  · exact checked2236
theorem derived2236 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2236 := by
  apply localUnsat_implies_entails f2236 [c2219, c168, c63, c76, c247, c347, c2081] c2236 unsat2236 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c347 := h 346 (by decide)
  have h6 : Entails.eval a c2081 := derived2081 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2237 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2237 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2100, some c2126, some c2094, some c2138, some c108, some c4, some c24, some c200, some c2236, some c2118, some c164, some c117, some c1192, some c280, some c146, some c142, some c2116, some c313, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2237 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2237 : lratChecker f2237 p2237 = .success := by decide +kernel
theorem unsat2237 : Unsatisfiable (PosFin 57) f2237 := by
  apply lratCheckerSound f2237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2237
  · intro a ha; simp [p2237] at ha; subst a; trivial
  · exact checked2237
theorem derived2237 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2237 := by
  apply localUnsat_implies_entails f2237 [c2219, c2100, c2126, c2094, c2138, c108, c4, c24, c200, c2236, c2118, c164, c117, c1192, c280, c146, c142, c2116, c313] c2237 unsat2237 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2100 := derived2100 a h
  have h2 : Entails.eval a c2126 := derived2126 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c2138 := derived2138 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c2236 := derived2236 a h
  have h10 : Entails.eval a c2118 := derived2118 a h
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c1192 := derived1192 a h
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c2116 := derived2116 a h
  have h18 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2238 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2238 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c69, some c2084, some c168, some c346, some c2118, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2238 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2238 : lratChecker f2238 p2238 = .success := by decide +kernel
theorem unsat2238 : Unsatisfiable (PosFin 57) f2238 := by
  apply lratCheckerSound f2238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2238
  · intro a ha; simp [p2238] at ha; subst a; trivial
  · exact checked2238
theorem derived2238 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2238 := by
  apply localUnsat_implies_entails f2238 [c2219, c69, c2084, c168, c346, c2118] c2238 unsat2238 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c2084 := derived2084 a h
  have h3 : Entails.eval a c168 := h 167 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c2118 := derived2118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2239 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2239 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2235, some c268, some c2100, some c2085, some c2094, some c2237, some c2238, some c1083, some c2214, some c111, some c2114, some c2148, some c2149, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2239 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2239 : lratChecker f2239 p2239 = .success := by decide +kernel
theorem unsat2239 : Unsatisfiable (PosFin 57) f2239 := by
  apply lratCheckerSound f2239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2239
  · intro a ha; simp [p2239] at ha; subst a; trivial
  · exact checked2239
theorem derived2239 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2239 := by
  apply localUnsat_implies_entails f2239 [c2219, c2235, c268, c2100, c2085, c2094, c2237, c2238, c1083, c2214, c111, c2114, c2148, c2149] c2239 unsat2239 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2235 := derived2235 a h
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2094 := derived2094 a h
  have h6 : Entails.eval a c2237 := derived2237 a h
  have h7 : Entails.eval a c2238 := derived2238 a h
  have h8 : Entails.eval a c1083 := derived1083 a h
  have h9 : Entails.eval a c2214 := derived2214 a h
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c2114 := derived2114 a h
  have h12 : Entails.eval a c2148 := derived2148 a h
  have h13 : Entails.eval a c2149 := derived2149 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2240 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2240 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2126, some c2085, some c314, some c133, some c2088, some c230, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2240 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2240 : lratChecker f2240 p2240 = .success := by decide +kernel
theorem unsat2240 : Unsatisfiable (PosFin 57) f2240 := by
  apply lratCheckerSound f2240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2240
  · intro a ha; simp [p2240] at ha; subst a; trivial
  · exact checked2240
theorem derived2240 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2240 := by
  apply localUnsat_implies_entails f2240 [c2126, c2085, c314, c133, c2088, c230] c2240 unsat2240 (by rfl) a
  have h0 : Entails.eval a c2126 := derived2126 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c2088 := derived2088 a h
  have h5 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2241 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2241 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c348, some c76, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2241 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2241 : lratChecker f2241 p2241 = .success := by decide +kernel
theorem unsat2241 : Unsatisfiable (PosFin 57) f2241 := by
  apply lratCheckerSound f2241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2241
  · intro a ha; simp [p2241] at ha; subst a; trivial
  · exact checked2241
theorem derived2241 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2241 := by
  apply localUnsat_implies_entails f2241 [c347, c348, c76] c2241 unsat2241 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c348 := h 347 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2242 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2242 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2100, some c2126, some c2085, some c2138, some c108, some c24, some c164, some c2118, some c2241, some c2081, some c247, some c246, some c104, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2242 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2242 : lratChecker f2242 p2242 = .success := by decide +kernel
theorem unsat2242 : Unsatisfiable (PosFin 57) f2242 := by
  apply lratCheckerSound f2242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2242
  · intro a ha; simp [p2242] at ha; subst a; trivial
  · exact checked2242
theorem derived2242 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2242 := by
  apply localUnsat_implies_entails f2242 [c2219, c2100, c2126, c2085, c2138, c108, c24, c164, c2118, c2241, c2081, c247, c246, c104] c2242 unsat2242 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2100 := derived2100 a h
  have h2 : Entails.eval a c2126 := derived2126 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2138 := derived2138 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c2118 := derived2118 a h
  have h9 : Entails.eval a c2241 := derived2241 a h
  have h10 : Entails.eval a c2081 := derived2081 a h
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2243 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2243 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c1083, some c164, some c69, some c2084, some c2118, some c348, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2243 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2243 : lratChecker f2243 p2243 = .success := by decide +kernel
theorem unsat2243 : Unsatisfiable (PosFin 57) f2243 := by
  apply lratCheckerSound f2243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2243
  · intro a ha; simp [p2243] at ha; subst a; trivial
  · exact checked2243
theorem derived2243 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2243 := by
  apply localUnsat_implies_entails f2243 [c24, c1083, c164, c69, c2084, c2118, c348] c2243 unsat2243 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c1083 := derived1083 a h
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c2084 := derived2084 a h
  have h5 : Entails.eval a c2118 := derived2118 a h
  have h6 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2244 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2244 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2235, some c2085, some c2094, some c268, some c2100, some c2126, some c2239, some c2091, some c2146, some c2092, some c200, some c2240, some c2242, some c2243, some c111, some c25, some c164, some c166, some c2117, some c63, some c2151, some c247, some c2134, some c2081, some c2087, some c272, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2244 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2244 : lratChecker f2244 p2244 = .success := by decide +kernel
theorem unsat2244 : Unsatisfiable (PosFin 57) f2244 := by
  apply lratCheckerSound f2244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2244
  · intro a ha; simp [p2244] at ha; subst a; trivial
  · exact checked2244
theorem derived2244 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2244 := by
  apply localUnsat_implies_entails f2244 [c2219, c2235, c2085, c2094, c268, c2100, c2126, c2239, c2091, c2146, c2092, c200, c2240, c2242, c2243, c111, c25, c164, c166, c2117, c63, c2151, c247, c2134, c2081, c2087, c272] c2244 unsat2244 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2235 := derived2235 a h
  have h2 : Entails.eval a c2085 := derived2085 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c2100 := derived2100 a h
  have h6 : Entails.eval a c2126 := derived2126 a h
  have h7 : Entails.eval a c2239 := derived2239 a h
  have h8 : Entails.eval a c2091 := derived2091 a h
  have h9 : Entails.eval a c2146 := derived2146 a h
  have h10 : Entails.eval a c2092 := derived2092 a h
  have h11 : Entails.eval a c200 := h 199 (by decide)
  have h12 : Entails.eval a c2240 := derived2240 a h
  have h13 : Entails.eval a c2242 := derived2242 a h
  have h14 : Entails.eval a c2243 := derived2243 a h
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c166 := h 165 (by decide)
  have h19 : Entails.eval a c2117 := derived2117 a h
  have h20 : Entails.eval a c63 := h 62 (by decide)
  have h21 : Entails.eval a c2151 := derived2151 a h
  have h22 : Entails.eval a c247 := h 246 (by decide)
  have h23 : Entails.eval a c2134 := derived2134 a h
  have h24 : Entails.eval a c2081 := derived2081 a h
  have h25 : Entails.eval a c2087 := derived2087 a h
  have h26 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2245 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2245 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2084, some c68, some c346, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p2245 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2245 : lratChecker f2245 p2245 = .success := by decide +kernel
theorem unsat2245 : Unsatisfiable (PosFin 57) f2245 := by
  apply lratCheckerSound f2245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2245
  · intro a ha; simp [p2245] at ha; subst a; trivial
  · exact checked2245
theorem derived2245 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2245 := by
  apply localUnsat_implies_entails f2245 [c2084, c68, c346] c2245 unsat2245 (by rfl) a
  have h0 : Entails.eval a c2084 := derived2084 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2246 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨39, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2246 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c1024, some c108, some c2245, some c1848, some c2154, some c2214, some c158, some c49, some c2091, some c2117, some c212, some c284, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2246 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2246 : lratChecker f2246 p2246 = .success := by decide +kernel
theorem unsat2246 : Unsatisfiable (PosFin 57) f2246 := by
  apply lratCheckerSound f2246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2246
  · intro a ha; simp [p2246] at ha; subst a; trivial
  · exact checked2246
theorem derived2246 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2246 := by
  apply localUnsat_implies_entails f2246 [c2219, c1024, c108, c2245, c1848, c2154, c2214, c158, c49, c2091, c2117, c212, c284] c2246 unsat2246 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c1024 := derived1024 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c2245 := derived2245 a h
  have h4 : Entails.eval a c1848 := derived1848 a h
  have h5 : Entails.eval a c2154 := derived2154 a h
  have h6 : Entails.eval a c2214 := derived2214 a h
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c2091 := derived2091 a h
  have h10 : Entails.eval a c2117 := derived2117 a h
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2247 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2247 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2094, some c2244, some c27, some c36, some c1024, some c108, some c2246, some c2146, some c2148, some c199, some c2150, some c2114, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2247 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2247 : lratChecker f2247 p2247 = .success := by decide +kernel
theorem unsat2247 : Unsatisfiable (PosFin 57) f2247 := by
  apply lratCheckerSound f2247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2247
  · intro a ha; simp [p2247] at ha; subst a; trivial
  · exact checked2247
theorem derived2247 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2247 := by
  apply localUnsat_implies_entails f2247 [c2219, c2085, c2094, c2244, c27, c36, c1024, c108, c2246, c2146, c2148, c199, c2150, c2114] c2247 unsat2247 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2244 := derived2244 a h
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c1024 := derived1024 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c2246 := derived2246 a h
  have h9 : Entails.eval a c2146 := derived2146 a h
  have h10 : Entails.eval a c2148 := derived2148 a h
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c2150 := derived2150 a h
  have h13 : Entails.eval a c2114 := derived2114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2248 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨21, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2248 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c112, some c5, some c204, some c2079, some c51, some c56, some c146, some c2116, some c53, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2248 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2248 : lratChecker f2248 p2248 = .success := by decide +kernel
theorem unsat2248 : Unsatisfiable (PosFin 57) f2248 := by
  apply lratCheckerSound f2248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2248
  · intro a ha; simp [p2248] at ha; subst a; trivial
  · exact checked2248
theorem derived2248 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2248 := by
  apply localUnsat_implies_entails f2248 [c2219, c112, c5, c204, c2079, c51, c56, c146, c2116, c53] c2248 unsat2248 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c2079 := derived2079 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c2116 := derived2116 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2249 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2249 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c53, some c146, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p2249 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2249 : lratChecker f2249 p2249 = .success := by decide +kernel
theorem unsat2249 : Unsatisfiable (PosFin 57) f2249 := by
  apply lratCheckerSound f2249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2249
  · intro a ha; simp [p2249] at ha; subst a; trivial
  · exact checked2249
theorem derived2249 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2249 := by
  apply localUnsat_implies_entails f2249 [c49, c53, c146] c2249 unsat2249 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2250 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2250 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2247, some c112, some c2235, some c268, some c1896, some c2229, some c2085, some c5, some c25, some c164, some c2117, some c2110, some c24, some c204, some c2079, some c2100, some c2094, some c2214, some c58, some c2084, some c2135, some c62, some c2248, some c2249, some c2116, some c272, some c2230, some c142, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2250 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2250 : lratChecker f2250 p2250 = .success := by decide +kernel
theorem unsat2250 : Unsatisfiable (PosFin 57) f2250 := by
  apply lratCheckerSound f2250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2250
  · intro a ha; simp [p2250] at ha; subst a; trivial
  · exact checked2250
theorem derived2250 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2250 := by
  apply localUnsat_implies_entails f2250 [c2219, c2247, c112, c2235, c268, c1896, c2229, c2085, c5, c25, c164, c2117, c2110, c24, c204, c2079, c2100, c2094, c2214, c58, c2084, c2135, c62, c2248, c2249, c2116, c272, c2230, c142] c2250 unsat2250 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2247 := derived2247 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c2235 := derived2235 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1896 := derived1896 a h
  have h6 : Entails.eval a c2229 := derived2229 a h
  have h7 : Entails.eval a c2085 := derived2085 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  have h11 : Entails.eval a c2117 := derived2117 a h
  have h12 : Entails.eval a c2110 := derived2110 a h
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c2079 := derived2079 a h
  have h16 : Entails.eval a c2100 := derived2100 a h
  have h17 : Entails.eval a c2094 := derived2094 a h
  have h18 : Entails.eval a c2214 := derived2214 a h
  have h19 : Entails.eval a c58 := h 57 (by decide)
  have h20 : Entails.eval a c2084 := derived2084 a h
  have h21 : Entails.eval a c2135 := derived2135 a h
  have h22 : Entails.eval a c62 := h 61 (by decide)
  have h23 : Entails.eval a c2248 := derived2248 a h
  have h24 : Entails.eval a c2249 := derived2249 a h
  have h25 : Entails.eval a c2116 := derived2116 a h
  have h26 : Entails.eval a c272 := h 271 (by decide)
  have h27 : Entails.eval a c2230 := derived2230 a h
  have h28 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2251 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨21, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2251 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c112, some c2079, some c2091, some c56, some c5, some c204, some c1896, some c2100, some c2134, some c2249, some c138, some c230, some c89, some c170, some c292, some c87, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2251 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2251 : lratChecker f2251 p2251 = .success := by decide +kernel
theorem unsat2251 : Unsatisfiable (PosFin 57) f2251 := by
  apply lratCheckerSound f2251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2251
  · intro a ha; simp [p2251] at ha; subst a; trivial
  · exact checked2251
theorem derived2251 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2251 := by
  apply localUnsat_implies_entails f2251 [c2219, c112, c2079, c2091, c56, c5, c204, c1896, c2100, c2134, c2249, c138, c230, c89, c170, c292, c87] c2251 unsat2251 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c2079 := derived2079 a h
  have h3 : Entails.eval a c2091 := derived2091 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c1896 := derived1896 a h
  have h8 : Entails.eval a c2100 := derived2100 a h
  have h9 : Entails.eval a c2134 := derived2134 a h
  have h10 : Entails.eval a c2249 := derived2249 a h
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2252 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2252 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2135, some c246, some c2108, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2252 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2252 : lratChecker f2252 p2252 = .success := by decide +kernel
theorem unsat2252 : Unsatisfiable (PosFin 57) f2252 := by
  apply lratCheckerSound f2252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2252
  · intro a ha; simp [p2252] at ha; subst a; trivial
  · exact checked2252
theorem derived2252 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2252 := by
  apply localUnsat_implies_entails f2252 [c2135, c246, c2108] c2252 unsat2252 (by rfl) a
  have h0 : Entails.eval a c2135 := derived2135 a h
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c2108 := derived2108 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2253 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2253 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2247, some c112, some c2235, some c268, some c1896, some c2229, some c2252, some c25, some c5, some c2085, some c2094, some c164, some c2250, some c24, some c2117, some c2251, some c2110, some c62, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2253 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2253 : lratChecker f2253 p2253 = .success := by decide +kernel
theorem unsat2253 : Unsatisfiable (PosFin 57) f2253 := by
  apply lratCheckerSound f2253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2253
  · intro a ha; simp [p2253] at ha; subst a; trivial
  · exact checked2253
theorem derived2253 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2253 := by
  apply localUnsat_implies_entails f2253 [c2247, c112, c2235, c268, c1896, c2229, c2252, c25, c5, c2085, c2094, c164, c2250, c24, c2117, c2251, c2110, c62] c2253 unsat2253 (by rfl) a
  have h0 : Entails.eval a c2247 := derived2247 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c2235 := derived2235 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c1896 := derived1896 a h
  have h5 : Entails.eval a c2229 := derived2229 a h
  have h6 : Entails.eval a c2252 := derived2252 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c2085 := derived2085 a h
  have h10 : Entails.eval a c2094 := derived2094 a h
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c2250 := derived2250 a h
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c2117 := derived2117 a h
  have h15 : Entails.eval a c2251 := derived2251 a h
  have h16 : Entails.eval a c2110 := derived2110 a h
  have h17 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2254 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2254 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2247, some c112, some c2235, some c2085, some c2094, some c268, some c2100, some c5, some c1896, some c204, some c2229, some c2252, some c2253, some c4, some c116, some c2114, some c49, some c62, some c146, some c2110, some c281, some c2117, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2254 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2254 : lratChecker f2254 p2254 = .success := by decide +kernel
theorem unsat2254 : Unsatisfiable (PosFin 57) f2254 := by
  apply lratCheckerSound f2254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2254
  · intro a ha; simp [p2254] at ha; subst a; trivial
  · exact checked2254
theorem derived2254 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2254 := by
  apply localUnsat_implies_entails f2254 [c2219, c2247, c112, c2235, c2085, c2094, c268, c2100, c5, c1896, c204, c2229, c2252, c2253, c4, c116, c2114, c49, c62, c146, c2110, c281, c2117] c2254 unsat2254 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2247 := derived2247 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c2235 := derived2235 a h
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2094 := derived2094 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c2100 := derived2100 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c1896 := derived1896 a h
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c2229 := derived2229 a h
  have h12 : Entails.eval a c2252 := derived2252 a h
  have h13 : Entails.eval a c2253 := derived2253 a h
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c2114 := derived2114 a h
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c2110 := derived2110 a h
  have h21 : Entails.eval a c281 := h 280 (by decide)
  have h22 : Entails.eval a c2117 := derived2117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2255 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2255 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2254, some c2247, some c112, some c2235, some c2085, some c199, some c2214, some c2126, some c58, some c2084, some c68, some c2245, some c2252, some c2122, some c188, some c224, some c1881, some c352, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2255 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2255 : lratChecker f2255 p2255 = .success := by decide +kernel
theorem unsat2255 : Unsatisfiable (PosFin 57) f2255 := by
  apply lratCheckerSound f2255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2255
  · intro a ha; simp [p2255] at ha; subst a; trivial
  · exact checked2255
theorem derived2255 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2255 := by
  apply localUnsat_implies_entails f2255 [c2219, c2254, c2247, c112, c2235, c2085, c199, c2214, c2126, c58, c2084, c68, c2245, c2252, c2122, c188, c224, c1881, c352] c2255 unsat2255 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2254 := derived2254 a h
  have h2 : Entails.eval a c2247 := derived2247 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c2235 := derived2235 a h
  have h5 : Entails.eval a c2085 := derived2085 a h
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c2214 := derived2214 a h
  have h8 : Entails.eval a c2126 := derived2126 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c2084 := derived2084 a h
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c2245 := derived2245 a h
  have h13 : Entails.eval a c2252 := derived2252 a h
  have h14 : Entails.eval a c2122 := derived2122 a h
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c1881 := derived1881 a h
  have h18 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2256 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2256 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c2094, some c2246, some c2249, some c224, some c18, some c158, some c164, some c68, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2256 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2256 : lratChecker f2256 p2256 = .success := by decide +kernel
theorem unsat2256 : Unsatisfiable (PosFin 57) f2256 := by
  apply lratCheckerSound f2256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2256
  · intro a ha; simp [p2256] at ha; subst a; trivial
  · exact checked2256
theorem derived2256 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2256 := by
  apply localUnsat_implies_entails f2256 [c200, c2094, c2246, c2249, c224, c18, c158, c164, c68] c2256 unsat2256 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2246 := derived2246 a h
  have h3 : Entails.eval a c2249 := derived2249 a h
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2257 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2257 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2254, some c2247, some c112, some c2085, some c2094, some c2255, some c2091, some c2093, some c56, some c212, some c2256, some c24, some c1083, some c68, some c1021, some c280, some c18, some c150, some c2134, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2257 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2257 : lratChecker f2257 p2257 = .success := by decide +kernel
theorem unsat2257 : Unsatisfiable (PosFin 57) f2257 := by
  apply lratCheckerSound f2257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2257
  · intro a ha; simp [p2257] at ha; subst a; trivial
  · exact checked2257
theorem derived2257 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2257 := by
  apply localUnsat_implies_entails f2257 [c2219, c2254, c2247, c112, c2085, c2094, c2255, c2091, c2093, c56, c212, c2256, c24, c1083, c68, c1021, c280, c18, c150, c2134] c2257 unsat2257 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2254 := derived2254 a h
  have h2 : Entails.eval a c2247 := derived2247 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2094 := derived2094 a h
  have h6 : Entails.eval a c2255 := derived2255 a h
  have h7 : Entails.eval a c2091 := derived2091 a h
  have h8 : Entails.eval a c2093 := derived2093 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c2256 := derived2256 a h
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c1083 := derived1083 a h
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c1021 := derived1021 a h
  have h16 : Entails.eval a c280 := h 279 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c150 := h 149 (by decide)
  have h19 : Entails.eval a c2134 := derived2134 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2258 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2258 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c2232, some c2115, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2258 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2258 : lratChecker f2258 p2258 = .success := by decide +kernel
theorem unsat2258 : Unsatisfiable (PosFin 57) f2258 := by
  apply lratCheckerSound f2258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2258
  · intro a ha; simp [p2258] at ha; subst a; trivial
  · exact checked2258
theorem derived2258 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2258 := by
  apply localUnsat_implies_entails f2258 [c108, c2232, c2115] c2258 unsat2258 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c2232 := derived2232 a h
  have h2 : Entails.eval a c2115 := derived2115 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2259 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2259 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2094, some c2247, some c112, some c2254, some c2258, some c2257, some c2146, some c4, some c116, some c2148, some c199, some c1783, some c204, some c2126, some c2114, some c146, some c2252, some c62, some c2110, some c281, some c2117, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2259 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2259 : lratChecker f2259 p2259 = .success := by decide +kernel
theorem unsat2259 : Unsatisfiable (PosFin 57) f2259 := by
  apply lratCheckerSound f2259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2259
  · intro a ha; simp [p2259] at ha; subst a; trivial
  · exact checked2259
theorem derived2259 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2259 := by
  apply localUnsat_implies_entails f2259 [c2219, c2085, c2094, c2247, c112, c2254, c2258, c2257, c2146, c4, c116, c2148, c199, c1783, c204, c2126, c2114, c146, c2252, c62, c2110, c281, c2117] c2259 unsat2259 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2247 := derived2247 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c2254 := derived2254 a h
  have h6 : Entails.eval a c2258 := derived2258 a h
  have h7 : Entails.eval a c2257 := derived2257 a h
  have h8 : Entails.eval a c2146 := derived2146 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c2148 := derived2148 a h
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c1783 := derived1783 a h
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c2126 := derived2126 a h
  have h16 : Entails.eval a c2114 := derived2114 a h
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c2252 := derived2252 a h
  have h19 : Entails.eval a c62 := h 61 (by decide)
  have h20 : Entails.eval a c2110 := derived2110 a h
  have h21 : Entails.eval a c281 := h 280 (by decide)
  have h22 : Entails.eval a c2117 := derived2117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2260 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2260 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c1967, some c2100, some c5, some c117, some c2129, some c200, some c4, some c116, some c52, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2260 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2260 : lratChecker f2260 p2260 = .success := by decide +kernel
theorem unsat2260 : Unsatisfiable (PosFin 57) f2260 := by
  apply lratCheckerSound f2260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2260
  · intro a ha; simp [p2260] at ha; subst a; trivial
  · exact checked2260
theorem derived2260 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2260 := by
  apply localUnsat_implies_entails f2260 [c2219, c1967, c2100, c5, c117, c2129, c200, c4, c116, c52] c2260 unsat2260 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c2100 := derived2100 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c2129 := derived2129 a h
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2261 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2261 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c1967, some c2094, some c200, some c1931, some c2129, some c199, some c2134, some c146, some c150, some c318, some c319, some c212, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2261 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2261 : lratChecker f2261 p2261 = .success := by decide +kernel
theorem unsat2261 : Unsatisfiable (PosFin 57) f2261 := by
  apply lratCheckerSound f2261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2261
  · intro a ha; simp [p2261] at ha; subst a; trivial
  · exact checked2261
theorem derived2261 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2261 := by
  apply localUnsat_implies_entails f2261 [c2219, c1967, c2094, c200, c1931, c2129, c199, c2134, c146, c150, c318, c319, c212] c2261 unsat2261 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c1967 := derived1967 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c1931 := derived1931 a h
  have h5 : Entails.eval a c2129 := derived2129 a h
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c2134 := derived2134 a h
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c319 := h 318 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2262 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2262 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2094, some c2235, some c2259, some c1967, some c2260, some c268, some c2261, some c2146, some c4, some c116, some c199, some c2126, some c2114, some c18, some c52, some c137, some c229, some c88, some c171, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2262 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2262 : lratChecker f2262 p2262 = .success := by decide +kernel
theorem unsat2262 : Unsatisfiable (PosFin 57) f2262 := by
  apply lratCheckerSound f2262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2262
  · intro a ha; simp [p2262] at ha; subst a; trivial
  · exact checked2262
theorem derived2262 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2262 := by
  apply localUnsat_implies_entails f2262 [c2219, c2085, c2094, c2235, c2259, c1967, c2260, c268, c2261, c2146, c4, c116, c199, c2126, c2114, c18, c52, c137, c229, c88, c171] c2262 unsat2262 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2235 := derived2235 a h
  have h4 : Entails.eval a c2259 := derived2259 a h
  have h5 : Entails.eval a c1967 := derived1967 a h
  have h6 : Entails.eval a c2260 := derived2260 a h
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c2261 := derived2261 a h
  have h9 : Entails.eval a c2146 := derived2146 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c2126 := derived2126 a h
  have h14 : Entails.eval a c2114 := derived2114 a h
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c229 := h 228 (by decide)
  have h19 : Entails.eval a c88 := h 87 (by decide)
  have h20 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2263 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2263 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2262, some c2085, some c2124, some c197, some c2100, some c12, some c261, some c111, some c2115, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2263 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2263 : lratChecker f2263 p2263 = .success := by decide +kernel
theorem unsat2263 : Unsatisfiable (PosFin 57) f2263 := by
  apply lratCheckerSound f2263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2263
  · intro a ha; simp [p2263] at ha; subst a; trivial
  · exact checked2263
theorem derived2263 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2263 := by
  apply localUnsat_implies_entails f2263 [c2219, c2262, c2085, c2124, c197, c2100, c12, c261, c111, c2115] c2263 unsat2263 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2262 := derived2262 a h
  have h2 : Entails.eval a c2085 := derived2085 a h
  have h3 : Entails.eval a c2124 := derived2124 a h
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c2100 := derived2100 a h
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c2115 := derived2115 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2264 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2264 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2263, some c2085, some c108, some c2115, some c2229, some c112, some c261, some c2100, some c24, some c2143, some c2138, some c2262, some c1192, some c2092, some c117, some c2236, some c2118, some c280, some c2116, some c48, some c134, some c141, some c81, some c2120, some c313, some c290, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2264 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2264 : lratChecker f2264 p2264 = .success := by decide +kernel
theorem unsat2264 : Unsatisfiable (PosFin 57) f2264 := by
  apply lratCheckerSound f2264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2264
  · intro a ha; simp [p2264] at ha; subst a; trivial
  · exact checked2264
theorem derived2264 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2264 := by
  apply localUnsat_implies_entails f2264 [c2219, c2263, c2085, c108, c2115, c2229, c112, c261, c2100, c24, c2143, c2138, c2262, c1192, c2092, c117, c2236, c2118, c280, c2116, c48, c134, c141, c81, c2120, c313, c290] c2264 unsat2264 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2263 := derived2263 a h
  have h2 : Entails.eval a c2085 := derived2085 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c2115 := derived2115 a h
  have h5 : Entails.eval a c2229 := derived2229 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c2100 := derived2100 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c2143 := derived2143 a h
  have h11 : Entails.eval a c2138 := derived2138 a h
  have h12 : Entails.eval a c2262 := derived2262 a h
  have h13 : Entails.eval a c1192 := derived1192 a h
  have h14 : Entails.eval a c2092 := derived2092 a h
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c2236 := derived2236 a h
  have h17 : Entails.eval a c2118 := derived2118 a h
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c2116 := derived2116 a h
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c134 := h 133 (by decide)
  have h22 : Entails.eval a c141 := h 140 (by decide)
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c2120 := derived2120 a h
  have h25 : Entails.eval a c313 := h 312 (by decide)
  have h26 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2265 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2265 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2263, some c108, some c2115, some c261, some c2229, some c112, some c2264, some c4, some c2242, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2265 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2265 : lratChecker f2265 p2265 = .success := by decide +kernel
theorem unsat2265 : Unsatisfiable (PosFin 57) f2265 := by
  apply lratCheckerSound f2265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2265
  · intro a ha; simp [p2265] at ha; subst a; trivial
  · exact checked2265
theorem derived2265 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2265 := by
  apply localUnsat_implies_entails f2265 [c2085, c2263, c108, c2115, c261, c2229, c112, c2264, c4, c2242] c2265 unsat2265 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2263 := derived2263 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c2115 := derived2115 a h
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c2229 := derived2229 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c2264 := derived2264 a h
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c2242 := derived2242 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2266 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2266 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2124, some c12, some c197, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2266 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2266 : lratChecker f2266 p2266 = .success := by decide +kernel
theorem unsat2266 : Unsatisfiable (PosFin 57) f2266 := by
  apply lratCheckerSound f2266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2266
  · intro a ha; simp [p2266] at ha; subst a; trivial
  · exact checked2266
theorem derived2266 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2266 := by
  apply localUnsat_implies_entails f2266 [c2219, c2124, c12, c197] c2266 unsat2266 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2124 := derived2124 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2267 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2267 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2262, some c2085, some c2265, some c1024, some c2266, some c2138, some c108, some c2258, some c2115, some c1229, some c62, some c246, some c2127, some c4, some c193, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2267 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2267 : lratChecker f2267 p2267 = .success := by decide +kernel
theorem unsat2267 : Unsatisfiable (PosFin 57) f2267 := by
  apply lratCheckerSound f2267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2267
  · intro a ha; simp [p2267] at ha; subst a; trivial
  · exact checked2267
theorem derived2267 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2267 := by
  apply localUnsat_implies_entails f2267 [c2262, c2085, c2265, c1024, c2266, c2138, c108, c2258, c2115, c1229, c62, c246, c2127, c4, c193] c2267 unsat2267 (by rfl) a
  have h0 : Entails.eval a c2262 := derived2262 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2265 := derived2265 a h
  have h3 : Entails.eval a c1024 := derived1024 a h
  have h4 : Entails.eval a c2266 := derived2266 a h
  have h5 : Entails.eval a c2138 := derived2138 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c2258 := derived2258 a h
  have h8 : Entails.eval a c2115 := derived2115 a h
  have h9 : Entails.eval a c1229 := derived1229 a h
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c2127 := derived2127 a h
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2268 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2268 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c261, some c2104, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2268 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2268 : lratChecker f2268 p2268 = .success := by decide +kernel
theorem unsat2268 : Unsatisfiable (PosFin 57) f2268 := by
  apply lratCheckerSound f2268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2268
  · intro a ha; simp [p2268] at ha; subst a; trivial
  · exact checked2268
theorem derived2268 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2268 := by
  apply localUnsat_implies_entails f2268 [c268, c261, c2104] c2268 unsat2268 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c2104 := derived2104 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2269 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨9, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2269 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2126, some c2262, some c2120, some c230, some c169, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2269 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2269 : lratChecker f2269 p2269 = .success := by decide +kernel
theorem unsat2269 : Unsatisfiable (PosFin 57) f2269 := by
  apply lratCheckerSound f2269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2269
  · intro a ha; simp [p2269] at ha; subst a; trivial
  · exact checked2269
theorem derived2269 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2269 := by
  apply localUnsat_implies_entails f2269 [c2126, c2262, c2120, c230, c169] c2269 unsat2269 (by rfl) a
  have h0 : Entails.eval a c2126 := derived2126 a h
  have h1 : Entails.eval a c2262 := derived2262 a h
  have h2 : Entails.eval a c2120 := derived2120 a h
  have h3 : Entails.eval a c230 := h 229 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2270 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2270 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c313, some c141, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2270 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2270 : lratChecker f2270 p2270 = .success := by decide +kernel
theorem unsat2270 : Unsatisfiable (PosFin 57) f2270 := by
  apply lratCheckerSound f2270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2270
  · intro a ha; simp [p2270] at ha; subst a; trivial
  · exact checked2270
theorem derived2270 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2270 := by
  apply localUnsat_implies_entails f2270 [c317, c313, c141] c2270 unsat2270 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2271 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2271 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2262, some c169, some c2124, some c2126, some c246, some c193, some c2133, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2271 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2271 : lratChecker f2271 p2271 = .success := by decide +kernel
theorem unsat2271 : Unsatisfiable (PosFin 57) f2271 := by
  apply lratCheckerSound f2271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2271
  · intro a ha; simp [p2271] at ha; subst a; trivial
  · exact checked2271
theorem derived2271 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2271 := by
  apply localUnsat_implies_entails f2271 [c2262, c169, c2124, c2126, c246, c193, c2133] c2271 unsat2271 (by rfl) a
  have h0 : Entails.eval a c2262 := derived2262 a h
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c2124 := derived2124 a h
  have h3 : Entails.eval a c2126 := derived2126 a h
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c2133 := derived2133 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2272 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨28, by decide⟩, true), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2272 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c2268, some c2100, some c2269, some c2262, some c2085, some c2116, some c2270, some c138, some c2124, some c2138, some c2129, some c2126, some c1967, some c117, some c5, some c835, some c296, some c899, some c727, some c90, some c169, some c2271, some c98, some c363, some c189, some c297, some c2133, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2272 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2272 : lratChecker f2272 p2272 = .success := by decide +kernel
theorem unsat2272 : Unsatisfiable (PosFin 57) f2272 := by
  apply lratCheckerSound f2272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2272
  · intro a ha; simp [p2272] at ha; subst a; trivial
  · exact checked2272
theorem derived2272 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2272 := by
  apply localUnsat_implies_entails f2272 [c2219, c2267, c2268, c2100, c2269, c2262, c2085, c2116, c2270, c138, c2124, c2138, c2129, c2126, c1967, c117, c5, c835, c296, c899, c727, c90, c169, c2271, c98, c363, c189, c297, c2133] c2272 unsat2272 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c2268 := derived2268 a h
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c2269 := derived2269 a h
  have h5 : Entails.eval a c2262 := derived2262 a h
  have h6 : Entails.eval a c2085 := derived2085 a h
  have h7 : Entails.eval a c2116 := derived2116 a h
  have h8 : Entails.eval a c2270 := derived2270 a h
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c2124 := derived2124 a h
  have h11 : Entails.eval a c2138 := derived2138 a h
  have h12 : Entails.eval a c2129 := derived2129 a h
  have h13 : Entails.eval a c2126 := derived2126 a h
  have h14 : Entails.eval a c1967 := derived1967 a h
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c835 := derived835 a h
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c899 := derived899 a h
  have h20 : Entails.eval a c727 := derived727 a h
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c169 := h 168 (by decide)
  have h23 : Entails.eval a c2271 := derived2271 a h
  have h24 : Entails.eval a c98 := h 97 (by decide)
  have h25 : Entails.eval a c363 := h 362 (by decide)
  have h26 : Entails.eval a c189 := h 188 (by decide)
  have h27 : Entails.eval a c297 := h 296 (by decide)
  have h28 : Entails.eval a c2133 := derived2133 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2273 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2273 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c2268, some c2100, some c2269, some c2085, some c2262, some c2124, some c2138, some c2129, some c2126, some c1967, some c2092, some c2116, some c2270, some c138, some c2272, some c2236, some c2117, some c161, some c165, some c70, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2273 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2273 : lratChecker f2273 p2273 = .success := by decide +kernel
theorem unsat2273 : Unsatisfiable (PosFin 57) f2273 := by
  apply lratCheckerSound f2273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2273
  · intro a ha; simp [p2273] at ha; subst a; trivial
  · exact checked2273
theorem derived2273 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2273 := by
  apply localUnsat_implies_entails f2273 [c2219, c2267, c2268, c2100, c2269, c2085, c2262, c2124, c2138, c2129, c2126, c1967, c2092, c2116, c2270, c138, c2272, c2236, c2117, c161, c165, c70] c2273 unsat2273 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c2268 := derived2268 a h
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c2269 := derived2269 a h
  have h5 : Entails.eval a c2085 := derived2085 a h
  have h6 : Entails.eval a c2262 := derived2262 a h
  have h7 : Entails.eval a c2124 := derived2124 a h
  have h8 : Entails.eval a c2138 := derived2138 a h
  have h9 : Entails.eval a c2129 := derived2129 a h
  have h10 : Entails.eval a c2126 := derived2126 a h
  have h11 : Entails.eval a c1967 := derived1967 a h
  have h12 : Entails.eval a c2092 := derived2092 a h
  have h13 : Entails.eval a c2116 := derived2116 a h
  have h14 : Entails.eval a c2270 := derived2270 a h
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c2272 := derived2272 a h
  have h17 : Entails.eval a c2236 := derived2236 a h
  have h18 : Entails.eval a c2117 := derived2117 a h
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2274 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2274 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c2268, some c2100, some c2269, some c2085, some c2262, some c2124, some c2138, some c2129, some c1967, some c117, some c5, some c2273, some c52, some c2163, some c24, some c138, some c161, some c281, some c70, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2274 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2274 : lratChecker f2274 p2274 = .success := by decide +kernel
theorem unsat2274 : Unsatisfiable (PosFin 57) f2274 := by
  apply lratCheckerSound f2274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2274
  · intro a ha; simp [p2274] at ha; subst a; trivial
  · exact checked2274
theorem derived2274 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2274 := by
  apply localUnsat_implies_entails f2274 [c2219, c2267, c2268, c2100, c2269, c2085, c2262, c2124, c2138, c2129, c1967, c117, c5, c2273, c52, c2163, c24, c138, c161, c281, c70] c2274 unsat2274 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c2268 := derived2268 a h
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c2269 := derived2269 a h
  have h5 : Entails.eval a c2085 := derived2085 a h
  have h6 : Entails.eval a c2262 := derived2262 a h
  have h7 : Entails.eval a c2124 := derived2124 a h
  have h8 : Entails.eval a c2138 := derived2138 a h
  have h9 : Entails.eval a c2129 := derived2129 a h
  have h10 : Entails.eval a c1967 := derived1967 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c2273 := derived2273 a h
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c2163 := derived2163 a h
  have h16 : Entails.eval a c24 := h 23 (by decide)
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  have h20 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2275 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2275 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c1967, some c2085, some c2268, some c5, some c117, some c2274, some c4, some c116, some c52, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2275 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2275 : lratChecker f2275 p2275 = .success := by decide +kernel
theorem unsat2275 : Unsatisfiable (PosFin 57) f2275 := by
  apply lratCheckerSound f2275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2275
  · intro a ha; simp [p2275] at ha; subst a; trivial
  · exact checked2275
theorem derived2275 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2275 := by
  apply localUnsat_implies_entails f2275 [c2219, c2267, c1967, c2085, c2268, c5, c117, c2274, c4, c116, c52] c2275 unsat2275 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2268 := derived2268 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c2274 := derived2274 a h
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2276 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2276 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c1242, some c5, some c2092, some c117, some c27, some c52, some c168, some c212, some c2118, some c282, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p2276 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2276 : lratChecker f2276 p2276 = .success := by decide +kernel
theorem unsat2276 : Unsatisfiable (PosFin 57) f2276 := by
  apply lratCheckerSound f2276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2276
  · intro a ha; simp [p2276] at ha; subst a; trivial
  · exact checked2276
theorem derived2276 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2276 := by
  apply localUnsat_implies_entails f2276 [c2219, c1242, c5, c2092, c117, c27, c52, c168, c212, c2118, c282] c2276 unsat2276 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c1242 := derived1242 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c2118 := derived2118 a h
  have h10 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2277 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2277 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2275, some c2085, some c163, some c161, some c224, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2277 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2277 : lratChecker f2277 p2277 = .success := by decide +kernel
theorem unsat2277 : Unsatisfiable (PosFin 57) f2277 := by
  apply lratCheckerSound f2277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2277
  · intro a ha; simp [p2277] at ha; subst a; trivial
  · exact checked2277
theorem derived2277 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2277 := by
  apply localUnsat_implies_entails f2277 [c2219, c2275, c2085, c163, c161, c224] c2277 unsat2277 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2275 := derived2275 a h
  have h2 : Entails.eval a c2085 := derived2085 a h
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2278 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2278 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2269, some c2267, some c1967, some c2262, some c46, some c134, some c141, some c144, some c318, some c2121, some c270, some c290, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2278 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2278 : lratChecker f2278 p2278 = .success := by decide +kernel
theorem unsat2278 : Unsatisfiable (PosFin 57) f2278 := by
  apply lratCheckerSound f2278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2278
  · intro a ha; simp [p2278] at ha; subst a; trivial
  · exact checked2278
theorem derived2278 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2278 := by
  apply localUnsat_implies_entails f2278 [c2219, c2269, c2267, c1967, c2262, c46, c134, c141, c144, c318, c2121, c270, c290] c2278 unsat2278 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2269 := derived2269 a h
  have h2 : Entails.eval a c2267 := derived2267 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c2262 := derived2262 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c2121 := derived2121 a h
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2279 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2279 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c1967, some c2085, some c2262, some c2266, some c2138, some c18, some c2277, some c23, some c2082, some c59, some c70, some c2122, some c2140, some c189, some c165, some c347, some c2109, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2279 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2279 : lratChecker f2279 p2279 = .success := by decide +kernel
theorem unsat2279 : Unsatisfiable (PosFin 57) f2279 := by
  apply lratCheckerSound f2279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2279
  · intro a ha; simp [p2279] at ha; subst a; trivial
  · exact checked2279
theorem derived2279 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2279 := by
  apply localUnsat_implies_entails f2279 [c2219, c2267, c1967, c2085, c2262, c2266, c2138, c18, c2277, c23, c2082, c59, c70, c2122, c2140, c189, c165, c347, c2109] c2279 unsat2279 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2262 := derived2262 a h
  have h5 : Entails.eval a c2266 := derived2266 a h
  have h6 : Entails.eval a c2138 := derived2138 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c2277 := derived2277 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c2082 := derived2082 a h
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c2122 := derived2122 a h
  have h14 : Entails.eval a c2140 := derived2140 a h
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  have h18 : Entails.eval a c2109 := derived2109 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2280 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2280 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c2262, some c2085, some c2266, some c2138, some c2279, some c3, some c2129, some c1955, some c199, some c2091, some c48, some c134, some c2121, some c84, some c175, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2280 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2280 : lratChecker f2280 p2280 = .success := by decide +kernel
theorem unsat2280 : Unsatisfiable (PosFin 57) f2280 := by
  apply lratCheckerSound f2280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2280
  · intro a ha; simp [p2280] at ha; subst a; trivial
  · exact checked2280
theorem derived2280 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2280 := by
  apply localUnsat_implies_entails f2280 [c2219, c2267, c2262, c2085, c2266, c2138, c2279, c3, c2129, c1955, c199, c2091, c48, c134, c2121, c84, c175] c2280 unsat2280 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c2262 := derived2262 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2266 := derived2266 a h
  have h5 : Entails.eval a c2138 := derived2138 a h
  have h6 : Entails.eval a c2279 := derived2279 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c2129 := derived2129 a h
  have h9 : Entails.eval a c1955 := derived1955 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c2091 := derived2091 a h
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c2121 := derived2121 a h
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2281 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2281 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2275, some c2267, some c1967, some c2262, some c2085, some c2124, some c2129, some c2138, some c2277, some c23, some c2082, some c70, some c347, some c2278, some c2136, some c2116, some c212, some c48, some c818, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2281 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2281 : lratChecker f2281 p2281 = .success := by decide +kernel
theorem unsat2281 : Unsatisfiable (PosFin 57) f2281 := by
  apply lratCheckerSound f2281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2281
  · intro a ha; simp [p2281] at ha; subst a; trivial
  · exact checked2281
theorem derived2281 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2281 := by
  apply localUnsat_implies_entails f2281 [c2219, c2275, c2267, c1967, c2262, c2085, c2124, c2129, c2138, c2277, c23, c2082, c70, c347, c2278, c2136, c2116, c212, c48, c818] c2281 unsat2281 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2275 := derived2275 a h
  have h2 : Entails.eval a c2267 := derived2267 a h
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c2262 := derived2262 a h
  have h5 : Entails.eval a c2085 := derived2085 a h
  have h6 : Entails.eval a c2124 := derived2124 a h
  have h7 : Entails.eval a c2129 := derived2129 a h
  have h8 : Entails.eval a c2138 := derived2138 a h
  have h9 : Entails.eval a c2277 := derived2277 a h
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c2082 := derived2082 a h
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c2278 := derived2278 a h
  have h15 : Entails.eval a c2136 := derived2136 a h
  have h16 : Entails.eval a c2116 := derived2116 a h
  have h17 : Entails.eval a c212 := h 211 (by decide)
  have h18 : Entails.eval a c48 := h 47 (by decide)
  have h19 : Entails.eval a c818 := derived818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2282 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨27, by decide⟩, true), (⟨45, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2282 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c135, some c238, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2282 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2282 : lratChecker f2282 p2282 = .success := by decide +kernel
theorem unsat2282 : Unsatisfiable (PosFin 57) f2282 := by
  apply lratCheckerSound f2282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2282
  · intro a ha; simp [p2282] at ha; subst a; trivial
  · exact checked2282
theorem derived2282 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2282 := by
  apply localUnsat_implies_entails f2282 [c3, c135, c238] c2282 unsat2282 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2283 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2283 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2281, some c2275, some c2267, some c1967, some c2085, some c2276, some c2280, some c2262, some c52, some c144, some c137, some c315, some c88, some c2282, some c2277, some c2082, some c59, some c155, some c191, some c189, some c27, some c361, some c90, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2283 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2283 : lratChecker f2283 p2283 = .success := by decide +kernel
theorem unsat2283 : Unsatisfiable (PosFin 57) f2283 := by
  apply lratCheckerSound f2283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2283
  · intro a ha; simp [p2283] at ha; subst a; trivial
  · exact checked2283
theorem derived2283 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2283 := by
  apply localUnsat_implies_entails f2283 [c2219, c2281, c2275, c2267, c1967, c2085, c2276, c2280, c2262, c52, c144, c137, c315, c88, c2282, c2277, c2082, c59, c155, c191, c189, c27, c361, c90] c2283 unsat2283 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2281 := derived2281 a h
  have h2 : Entails.eval a c2275 := derived2275 a h
  have h3 : Entails.eval a c2267 := derived2267 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c2085 := derived2085 a h
  have h6 : Entails.eval a c2276 := derived2276 a h
  have h7 : Entails.eval a c2280 := derived2280 a h
  have h8 : Entails.eval a c2262 := derived2262 a h
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c315 := h 314 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c2282 := derived2282 a h
  have h15 : Entails.eval a c2277 := derived2277 a h
  have h16 : Entails.eval a c2082 := derived2082 a h
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c155 := h 154 (by decide)
  have h19 : Entails.eval a c191 := h 190 (by decide)
  have h20 : Entails.eval a c189 := h 188 (by decide)
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c361 := h 360 (by decide)
  have h23 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2284 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2284 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2275, some c2267, some c2085, some c2281, some c199, some c2091, some c2093, some c2283, some c212, some c56, some c314, some c27, some c207, some c155, some c284, some c2081, some c2082, some c2117, some c183, some c349, some c246, some c2084, some c104, some c2138, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2284 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2284 : lratChecker f2284 p2284 = .success := by decide +kernel
theorem unsat2284 : Unsatisfiable (PosFin 57) f2284 := by
  apply lratCheckerSound f2284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2284
  · intro a ha; simp [p2284] at ha; subst a; trivial
  · exact checked2284
theorem derived2284 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2284 := by
  apply localUnsat_implies_entails f2284 [c2219, c2275, c2267, c2085, c2281, c199, c2091, c2093, c2283, c212, c56, c314, c27, c207, c155, c284, c2081, c2082, c2117, c183, c349, c246, c2084, c104, c2138] c2284 unsat2284 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2275 := derived2275 a h
  have h2 : Entails.eval a c2267 := derived2267 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2281 := derived2281 a h
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c2091 := derived2091 a h
  have h7 : Entails.eval a c2093 := derived2093 a h
  have h8 : Entails.eval a c2283 := derived2283 a h
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c207 := h 206 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c2081 := derived2081 a h
  have h17 : Entails.eval a c2082 := derived2082 a h
  have h18 : Entails.eval a c2117 := derived2117 a h
  have h19 : Entails.eval a c183 := h 182 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  have h21 : Entails.eval a c246 := h 245 (by decide)
  have h22 : Entails.eval a c2084 := derived2084 a h
  have h23 : Entails.eval a c104 := h 103 (by decide)
  have h24 : Entails.eval a c2138 := derived2138 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2285 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2285 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2284, some c24, some c2275, some c36, some c2115, some c2267, some c2262, some c2124, some c2129, some c2269, some c2138, some c2277, some c2163, some c70, some c852, some c138, some c212, some c281, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2285 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2285 : lratChecker f2285 p2285 = .success := by decide +kernel
theorem unsat2285 : Unsatisfiable (PosFin 57) f2285 := by
  apply lratCheckerSound f2285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2285
  · intro a ha; simp [p2285] at ha; subst a; trivial
  · exact checked2285
theorem derived2285 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2285 := by
  apply localUnsat_implies_entails f2285 [c2085, c2284, c24, c2275, c36, c2115, c2267, c2262, c2124, c2129, c2269, c2138, c2277, c2163, c70, c852, c138, c212, c281] c2285 unsat2285 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2284 := derived2284 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c2275 := derived2275 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c2115 := derived2115 a h
  have h6 : Entails.eval a c2267 := derived2267 a h
  have h7 : Entails.eval a c2262 := derived2262 a h
  have h8 : Entails.eval a c2124 := derived2124 a h
  have h9 : Entails.eval a c2129 := derived2129 a h
  have h10 : Entails.eval a c2269 := derived2269 a h
  have h11 : Entails.eval a c2138 := derived2138 a h
  have h12 : Entails.eval a c2277 := derived2277 a h
  have h13 : Entails.eval a c2163 := derived2163 a h
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c852 := derived852 a h
  have h16 : Entails.eval a c138 := h 137 (by decide)
  have h17 : Entails.eval a c212 := h 211 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2286 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2286 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c3, some c1967, some c2262, some c2282, some c135, some c172, some c2121, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2286 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2286 : lratChecker f2286 p2286 = .success := by decide +kernel
theorem unsat2286 : Unsatisfiable (PosFin 57) f2286 := by
  apply lratCheckerSound f2286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2286
  · intro a ha; simp [p2286] at ha; subst a; trivial
  · exact checked2286
theorem derived2286 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2286 := by
  apply localUnsat_implies_entails f2286 [c2219, c2267, c3, c1967, c2262, c2282, c135, c172, c2121] c2286 unsat2286 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1967 := derived1967 a h
  have h4 : Entails.eval a c2262 := derived2262 a h
  have h5 : Entails.eval a c2282 := derived2282 a h
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c2121 := derived2121 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2287 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2287 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c1967, some c2262, some c318, some c315, some c144, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2287 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2287 : lratChecker f2287 p2287 = .success := by decide +kernel
theorem unsat2287 : Unsatisfiable (PosFin 57) f2287 := by
  apply lratCheckerSound f2287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2287
  · intro a ha; simp [p2287] at ha; subst a; trivial
  · exact checked2287
theorem derived2287 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2287 := by
  apply localUnsat_implies_entails f2287 [c2219, c2267, c1967, c2262, c318, c315, c144] c2287 unsat2287 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  have h3 : Entails.eval a c2262 := derived2262 a h
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2288 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2288 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2267, some c2285, some c2100, some c2085, some c2275, some c2284, some c2143, some c36, some c199, some c2091, some c56, some c212, some c2287, some c2286, some c2277, some c23, some c59, some c2122, some c191, some c2082, some c155, some c24, some c2115, some c2252, some c345, some c58, some c350, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2288 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2288 : lratChecker f2288 p2288 = .success := by decide +kernel
theorem unsat2288 : Unsatisfiable (PosFin 57) f2288 := by
  apply lratCheckerSound f2288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2288
  · intro a ha; simp [p2288] at ha; subst a; trivial
  · exact checked2288
theorem derived2288 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2288 := by
  apply localUnsat_implies_entails f2288 [c2219, c2267, c2285, c2100, c2085, c2275, c2284, c2143, c36, c199, c2091, c56, c212, c2287, c2286, c2277, c23, c59, c2122, c191, c2082, c155, c24, c2115, c2252, c345, c58, c350] c2288 unsat2288 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2267 := derived2267 a h
  have h2 : Entails.eval a c2285 := derived2285 a h
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2275 := derived2275 a h
  have h6 : Entails.eval a c2284 := derived2284 a h
  have h7 : Entails.eval a c2143 := derived2143 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c2091 := derived2091 a h
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  have h13 : Entails.eval a c2287 := derived2287 a h
  have h14 : Entails.eval a c2286 := derived2286 a h
  have h15 : Entails.eval a c2277 := derived2277 a h
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c2122 := derived2122 a h
  have h19 : Entails.eval a c191 := h 190 (by decide)
  have h20 : Entails.eval a c2082 := derived2082 a h
  have h21 : Entails.eval a c155 := h 154 (by decide)
  have h22 : Entails.eval a c24 := h 23 (by decide)
  have h23 : Entails.eval a c2115 := derived2115 a h
  have h24 : Entails.eval a c2252 := derived2252 a h
  have h25 : Entails.eval a c345 := h 344 (by decide)
  have h26 : Entails.eval a c58 := h 57 (by decide)
  have h27 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2289 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2275, some c2267, some c2085, some c2284, some c36, some c2143, some c24, some c2285, some c199, some c2100, some c2091, some c56, some c212, some c2287, some c2286, some c2277, some c23, some c2082, some c59, some c155, some c191, some c2122, some c2288, some c338, some c2138, some c1963, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2289 : lratChecker f2289 p2289 = .success := by decide +kernel
theorem unsat2289 : Unsatisfiable (PosFin 57) f2289 := by
  apply lratCheckerSound f2289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2289
  · intro a ha; simp [p2289] at ha; subst a; trivial
  · exact checked2289
theorem derived2289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2289 := by
  apply localUnsat_implies_entails f2289 [c2219, c2275, c2267, c2085, c2284, c36, c2143, c24, c2285, c199, c2100, c2091, c56, c212, c2287, c2286, c2277, c23, c2082, c59, c155, c191, c2122, c2288, c338, c2138, c1963] c2289 unsat2289 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2275 := derived2275 a h
  have h2 : Entails.eval a c2267 := derived2267 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2284 := derived2284 a h
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c2143 := derived2143 a h
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c2285 := derived2285 a h
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c2100 := derived2100 a h
  have h11 : Entails.eval a c2091 := derived2091 a h
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c212 := h 211 (by decide)
  have h14 : Entails.eval a c2287 := derived2287 a h
  have h15 : Entails.eval a c2286 := derived2286 a h
  have h16 : Entails.eval a c2277 := derived2277 a h
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c2082 := derived2082 a h
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c155 := h 154 (by decide)
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c2122 := derived2122 a h
  have h23 : Entails.eval a c2288 := derived2288 a h
  have h24 : Entails.eval a c338 := h 337 (by decide)
  have h25 : Entails.eval a c2138 := derived2138 a h
  have h26 : Entails.eval a c1963 := derived1963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2290 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2289, some c116, some c4, some c2267, some c1967, some c2262, some c2146, some c199, some c2124, some c46, some c144, some c52, some c134, some c2138, some c2269, some c2129, some c2287, some c2275, some c2276, some c2140, some c2121, some c224, some c290, some c1626, some c281, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2290 : lratChecker f2290 p2290 = .success := by decide +kernel
theorem unsat2290 : Unsatisfiable (PosFin 57) f2290 := by
  apply lratCheckerSound f2290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2290
  · intro a ha; simp [p2290] at ha; subst a; trivial
  · exact checked2290
theorem derived2290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2290 := by
  apply localUnsat_implies_entails f2290 [c2219, c2085, c2289, c116, c4, c2267, c1967, c2262, c2146, c199, c2124, c46, c144, c52, c134, c2138, c2269, c2129, c2287, c2275, c2276, c2140, c2121, c224, c290, c1626, c281] c2290 unsat2290 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2289 := derived2289 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c2267 := derived2267 a h
  have h6 : Entails.eval a c1967 := derived1967 a h
  have h7 : Entails.eval a c2262 := derived2262 a h
  have h8 : Entails.eval a c2146 := derived2146 a h
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c2124 := derived2124 a h
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c134 := h 133 (by decide)
  have h15 : Entails.eval a c2138 := derived2138 a h
  have h16 : Entails.eval a c2269 := derived2269 a h
  have h17 : Entails.eval a c2129 := derived2129 a h
  have h18 : Entails.eval a c2287 := derived2287 a h
  have h19 : Entails.eval a c2275 := derived2275 a h
  have h20 : Entails.eval a c2276 := derived2276 a h
  have h21 : Entails.eval a c2140 := derived2140 a h
  have h22 : Entails.eval a c2121 := derived2121 a h
  have h23 : Entails.eval a c224 := h 223 (by decide)
  have h24 : Entails.eval a c290 := h 289 (by decide)
  have h25 : Entails.eval a c1626 := derived1626 a h
  have h26 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2291 : DefaultClause 57 := directClause ((⟨50, by decide⟩, false) :: (⟨49, by decide⟩, true) :: (⟨2, by decide⟩, false) :: (⟨4, by decide⟩, false) :: (⟨6, by decide⟩, true) :: (⟨55, by decide⟩, true) :: (⟨8, by decide⟩, false) :: (⟨3, by decide⟩, true) :: (⟨5, by decide⟩, true) :: (⟨11, by decide⟩, false) :: (⟨54, by decide⟩, true) :: (⟨9, by decide⟩, true) :: (⟨10, by decide⟩, true) :: (⟨14, by decide⟩, false) :: (⟨17, by decide⟩, false) :: (⟨16, by decide⟩, false) :: (⟨19, by decide⟩, true) :: (⟨20, by decide⟩, true) :: (⟨21, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨23, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨12, by decide⟩, true) :: (⟨27, by decide⟩, true) :: (⟨29, by decide⟩, false) :: (⟨25, by decide⟩, false) :: (⟨31, by decide⟩, true) :: (⟨32, by decide⟩, false) :: (⟨28, by decide⟩, false) :: (⟨22, by decide⟩, false) :: (⟨30, by decide⟩, true) :: (⟨35, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨33, by decide⟩, false) :: (⟨38, by decide⟩, false) :: (⟨39, by decide⟩, true) :: (⟨52, by decide⟩, true) :: (⟨40, by decide⟩, true) :: (⟨42, by decide⟩, false) :: (⟨36, by decide⟩, false) :: (⟨41, by decide⟩, false) :: (⟨37, by decide⟩, true) :: (⟨47, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, true) :: (⟨43, by decide⟩, false) :: (⟨48, by decide⟩, true) :: (⟨51, by decide⟩, false) :: (⟨53, by decide⟩, false) :: (⟨56, by decide⟩, false) :: (⟨46, by decide⟩, true) :: []) (by decide +kernel) (by decide +kernel)
def f2291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2107, some c27, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p2291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2291 : lratChecker f2291 p2291 = .success := by decide +kernel
theorem unsat2291 : Unsatisfiable (PosFin 57) f2291 := by
  apply lratCheckerSound f2291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2291
  · intro a ha; simp [p2291] at ha; subst a; trivial
  · exact checked2291
theorem derived2291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2291 := by
  apply localUnsat_implies_entails f2291 [c2219, c2107, c27] c2291 unsat2291 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2107 := derived2107 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2292 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2219, some c2085, some c2262, some c2267, some c1967, some c2275, some c2289, some c2146, some c4, some c116, some c199, some c2276, some c2287, some c2126, some c2124, some c2129, some c2269, some c2138, some c46, some c134, some c818, some c141, some c144, some c82, some c52, some c171, some c18, some c229, some c2290, some c2145, some c2131, some c23, some c84, some c2270, some c163, some c296, some c290, some c224, some c324, some c280, some c1626, some c61, some c167, some c297, some c307, some c2081, some c2106, some c362, some c191, some c195, some c338, some c2291, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]]
theorem checked2292 : lratChecker f2292 p2292 = .success := by decide +kernel
theorem unsat2292 : Unsatisfiable (PosFin 57) f2292 := by
  apply lratCheckerSound f2292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2292
  · intro a ha; simp [p2292] at ha; subst a; trivial
  · exact checked2292
theorem derived2292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2292 := by
  apply localUnsat_implies_entails f2292 [c2219, c2085, c2262, c2267, c1967, c2275, c2289, c2146, c4, c116, c199, c2276, c2287, c2126, c2124, c2129, c2269, c2138, c46, c134, c818, c141, c144, c82, c52, c171, c18, c229, c2290, c2145, c2131, c23, c84, c2270, c163, c296, c290, c224, c324, c280, c1626, c61, c167, c297, c307, c2081, c2106, c362, c191, c195, c338, c2291] c2292 unsat2292 (by rfl) a
  have h0 : Entails.eval a c2219 := derived2219 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2262 := derived2262 a h
  have h3 : Entails.eval a c2267 := derived2267 a h
  have h4 : Entails.eval a c1967 := derived1967 a h
  have h5 : Entails.eval a c2275 := derived2275 a h
  have h6 : Entails.eval a c2289 := derived2289 a h
  have h7 : Entails.eval a c2146 := derived2146 a h
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c2276 := derived2276 a h
  have h12 : Entails.eval a c2287 := derived2287 a h
  have h13 : Entails.eval a c2126 := derived2126 a h
  have h14 : Entails.eval a c2124 := derived2124 a h
  have h15 : Entails.eval a c2129 := derived2129 a h
  have h16 : Entails.eval a c2269 := derived2269 a h
  have h17 : Entails.eval a c2138 := derived2138 a h
  have h18 : Entails.eval a c46 := h 45 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c818 := derived818 a h
  have h21 : Entails.eval a c141 := h 140 (by decide)
  have h22 : Entails.eval a c144 := h 143 (by decide)
  have h23 : Entails.eval a c82 := h 81 (by decide)
  have h24 : Entails.eval a c52 := h 51 (by decide)
  have h25 : Entails.eval a c171 := h 170 (by decide)
  have h26 : Entails.eval a c18 := h 17 (by decide)
  have h27 : Entails.eval a c229 := h 228 (by decide)
  have h28 : Entails.eval a c2290 := derived2290 a h
  have h29 : Entails.eval a c2145 := derived2145 a h
  have h30 : Entails.eval a c2131 := derived2131 a h
  have h31 : Entails.eval a c23 := h 22 (by decide)
  have h32 : Entails.eval a c84 := h 83 (by decide)
  have h33 : Entails.eval a c2270 := derived2270 a h
  have h34 : Entails.eval a c163 := h 162 (by decide)
  have h35 : Entails.eval a c296 := h 295 (by decide)
  have h36 : Entails.eval a c290 := h 289 (by decide)
  have h37 : Entails.eval a c224 := h 223 (by decide)
  have h38 : Entails.eval a c324 := h 323 (by decide)
  have h39 : Entails.eval a c280 := h 279 (by decide)
  have h40 : Entails.eval a c1626 := derived1626 a h
  have h41 : Entails.eval a c61 := h 60 (by decide)
  have h42 : Entails.eval a c167 := h 166 (by decide)
  have h43 : Entails.eval a c297 := h 296 (by decide)
  have h44 : Entails.eval a c307 := h 306 (by decide)
  have h45 : Entails.eval a c2081 := derived2081 a h
  have h46 : Entails.eval a c2106 := derived2106 a h
  have h47 : Entails.eval a c362 := h 361 (by decide)
  have h48 : Entails.eval a c191 := h 190 (by decide)
  have h49 : Entails.eval a c195 := h 194 (by decide)
  have h50 : Entails.eval a c338 := h 337 (by decide)
  have h51 : Entails.eval a c2291 := derived2291 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2293 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2292, some c1147, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p2293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2293 : lratChecker f2293 p2293 = .success := by decide +kernel
theorem unsat2293 : Unsatisfiable (PosFin 57) f2293 := by
  apply lratCheckerSound f2293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2293
  · intro a ha; simp [p2293] at ha; subst a; trivial
  · exact checked2293
theorem derived2293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2293 := by
  apply localUnsat_implies_entails f2293 [c2292, c1147] c2293 unsat2293 (by rfl) a
  have h0 : Entails.eval a c2292 := derived2292 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2294 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2292, some c2219, some c2010, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p2294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2294 : lratChecker f2294 p2294 = .success := by decide +kernel
theorem unsat2294 : Unsatisfiable (PosFin 57) f2294 := by
  apply lratCheckerSound f2294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2294
  · intro a ha; simp [p2294] at ha; subst a; trivial
  · exact checked2294
theorem derived2294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2294 := by
  apply localUnsat_implies_entails f2294 [c2292, c2219, c2010] c2294 unsat2294 (by rfl) a
  have h0 : Entails.eval a c2292 := derived2292 a h
  have h1 : Entails.eval a c2219 := derived2219 a h
  have h2 : Entails.eval a c2010 := derived2010 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2295 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2294, some c2219, some c2292, some c2293, some c1216, some c1261, some c261, some c204, some c1967, some c2144, some c2124, some c108, some c2229, some c2096, some c112, some c1884, some c166, some c226, some c2118, some c165, some c348, some c2083, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p2295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2295 : lratChecker f2295 p2295 = .success := by decide +kernel
theorem unsat2295 : Unsatisfiable (PosFin 57) f2295 := by
  apply lratCheckerSound f2295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2295
  · intro a ha; simp [p2295] at ha; subst a; trivial
  · exact checked2295
theorem derived2295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2295 := by
  apply localUnsat_implies_entails f2295 [c2294, c2219, c2292, c2293, c1216, c1261, c261, c204, c1967, c2144, c2124, c108, c2229, c2096, c112, c1884, c166, c226, c2118, c165, c348, c2083] c2295 unsat2295 (by rfl) a
  have h0 : Entails.eval a c2294 := derived2294 a h
  have h1 : Entails.eval a c2219 := derived2219 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c2293 := derived2293 a h
  have h4 : Entails.eval a c1216 := derived1216 a h
  have h5 : Entails.eval a c1261 := derived1261 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c1967 := derived1967 a h
  have h9 : Entails.eval a c2144 := derived2144 a h
  have h10 : Entails.eval a c2124 := derived2124 a h
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c2229 := derived2229 a h
  have h13 : Entails.eval a c2096 := derived2096 a h
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c1884 := derived1884 a h
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c226 := h 225 (by decide)
  have h18 : Entails.eval a c2118 := derived2118 a h
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c348 := h 347 (by decide)
  have h21 : Entails.eval a c2083 := derived2083 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2296 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2295, some c2293, some c2292, some c2094, some c1024, some c2266, some c108, some c2138, some c1229, some c26, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2296 : lratChecker f2296 p2296 = .success := by decide +kernel
theorem unsat2296 : Unsatisfiable (PosFin 57) f2296 := by
  apply lratCheckerSound f2296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2296
  · intro a ha; simp [p2296] at ha; subst a; trivial
  · exact checked2296
theorem derived2296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2296 := by
  apply localUnsat_implies_entails f2296 [c2295, c2293, c2292, c2094, c1024, c2266, c108, c2138, c1229, c26] c2296 unsat2296 (by rfl) a
  have h0 : Entails.eval a c2295 := derived2295 a h
  have h1 : Entails.eval a c2293 := derived2293 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c1024 := derived1024 a h
  have h5 : Entails.eval a c2266 := derived2266 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c2138 := derived2138 a h
  have h8 : Entails.eval a c1229 := derived1229 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2297 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c111, some c2266, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2297 : lratChecker f2297 p2297 = .success := by decide +kernel
theorem unsat2297 : Unsatisfiable (PosFin 57) f2297 := by
  apply lratCheckerSound f2297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2297
  · intro a ha; simp [p2297] at ha; subst a; trivial
  · exact checked2297
theorem derived2297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2297 := by
  apply localUnsat_implies_entails f2297 [c108, c111, c2266] c2297 unsat2297 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c2266 := derived2266 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2298 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2293, some c2219, some c2295, some c2292, some c2136, some c2099, some c168, some c228, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2298 : lratChecker f2298 p2298 = .success := by decide +kernel
theorem unsat2298 : Unsatisfiable (PosFin 57) f2298 := by
  apply lratCheckerSound f2298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2298
  · intro a ha; simp [p2298] at ha; subst a; trivial
  · exact checked2298
theorem derived2298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2298 := by
  apply localUnsat_implies_entails f2298 [c2293, c2219, c2295, c2292, c2136, c2099, c168, c228] c2298 unsat2298 (by rfl) a
  have h0 : Entails.eval a c2293 := derived2293 a h
  have h1 : Entails.eval a c2219 := derived2219 a h
  have h2 : Entails.eval a c2295 := derived2295 a h
  have h3 : Entails.eval a c2292 := derived2292 a h
  have h4 : Entails.eval a c2136 := derived2136 a h
  have h5 : Entails.eval a c2099 := derived2099 a h
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2299 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2295, some c2293, some c2292, some c40, some c820, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2299 : lratChecker f2299 p2299 = .success := by decide +kernel
theorem unsat2299 : Unsatisfiable (PosFin 57) f2299 := by
  apply lratCheckerSound f2299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2299
  · intro a ha; simp [p2299] at ha; subst a; trivial
  · exact checked2299
theorem derived2299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2299 := by
  apply localUnsat_implies_entails f2299 [c2295, c2293, c2292, c40, c820] c2299 unsat2299 (by rfl) a
  have h0 : Entails.eval a c2295 := derived2295 a h
  have h1 : Entails.eval a c2293 := derived2293 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c820 := derived820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2300 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2293, some c2292, some c201, some c2124, some c2299, some c2142, some c110, some c2091, some c2298, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2300 : lratChecker f2300 p2300 = .success := by decide +kernel
theorem unsat2300 : Unsatisfiable (PosFin 57) f2300 := by
  apply lratCheckerSound f2300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2300
  · intro a ha; simp [p2300] at ha; subst a; trivial
  · exact checked2300
theorem derived2300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2300 := by
  apply localUnsat_implies_entails f2300 [c2293, c2292, c201, c2124, c2299, c2142, c110, c2091, c2298] c2300 unsat2300 (by rfl) a
  have h0 : Entails.eval a c2293 := derived2293 a h
  have h1 : Entails.eval a c2292 := derived2292 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c2124 := derived2124 a h
  have h4 : Entails.eval a c2299 := derived2299 a h
  have h5 : Entails.eval a c2142 := derived2142 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c2091 := derived2091 a h
  have h8 : Entails.eval a c2298 := derived2298 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2301 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2293, some c2219, some c2292, some c2295, some c2300, some c199, some c2090, some c1100, some c154, some c165, some c2083, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2301 : lratChecker f2301 p2301 = .success := by decide +kernel
theorem unsat2301 : Unsatisfiable (PosFin 57) f2301 := by
  apply lratCheckerSound f2301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2301
  · intro a ha; simp [p2301] at ha; subst a; trivial
  · exact checked2301
theorem derived2301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2301 := by
  apply localUnsat_implies_entails f2301 [c2293, c2219, c2292, c2295, c2300, c199, c2090, c1100, c154, c165, c2083] c2301 unsat2301 (by rfl) a
  have h0 : Entails.eval a c2293 := derived2293 a h
  have h1 : Entails.eval a c2219 := derived2219 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c2295 := derived2295 a h
  have h4 : Entails.eval a c2300 := derived2300 a h
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c2090 := derived2090 a h
  have h7 : Entails.eval a c1100 := derived1100 a h
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c2083 := derived2083 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2302 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2293, some c2296, some c2086, some c201, some c2297, some c2301, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2302 : lratChecker f2302 p2302 = .success := by decide +kernel
theorem unsat2302 : Unsatisfiable (PosFin 57) f2302 := by
  apply lratCheckerSound f2302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2302
  · intro a ha; simp [p2302] at ha; subst a; trivial
  · exact checked2302
theorem derived2302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2302 := by
  apply localUnsat_implies_entails f2302 [c2293, c2296, c2086, c201, c2297, c2301] c2302 unsat2302 (by rfl) a
  have h0 : Entails.eval a c2293 := derived2293 a h
  have h1 : Entails.eval a c2296 := derived2296 a h
  have h2 : Entails.eval a c2086 := derived2086 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c2297 := derived2297 a h
  have h5 : Entails.eval a c2301 := derived2301 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2303 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2293, some c2294, some c2295, some c2292, some c2219, some c2302, some c2296, some c2086, some c108, some c111, some c2297, some c2144, some c202, some c204, some c1100, some c2091, some c2093, some c2092, some c159, some c2110, some c58, some c2084, some c2245, some c68, some c2137, some c187, some c2105, some c185, some c154, some c27, some c352, some c2119, some c102, some c2041, some c56, some c342, some c341, some c245, some c210, some c303, some c313, some c143, some c133, some c229, some c321, some c179, some c359, some c368, some c85, some c289, some c2128, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]]
theorem checked2303 : lratChecker f2303 p2303 = .success := by decide +kernel
theorem unsat2303 : Unsatisfiable (PosFin 57) f2303 := by
  apply lratCheckerSound f2303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2303
  · intro a ha; simp [p2303] at ha; subst a; trivial
  · exact checked2303
theorem derived2303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2303 := by
  apply localUnsat_implies_entails f2303 [c2293, c2294, c2295, c2292, c2219, c2302, c2296, c2086, c108, c111, c2297, c2144, c202, c204, c1100, c2091, c2093, c2092, c159, c2110, c58, c2084, c2245, c68, c2137, c187, c2105, c185, c154, c27, c352, c2119, c102, c2041, c56, c342, c341, c245, c210, c303, c313, c143, c133, c229, c321, c179, c359, c368, c85, c289, c2128] c2303 unsat2303 (by rfl) a
  have h0 : Entails.eval a c2293 := derived2293 a h
  have h1 : Entails.eval a c2294 := derived2294 a h
  have h2 : Entails.eval a c2295 := derived2295 a h
  have h3 : Entails.eval a c2292 := derived2292 a h
  have h4 : Entails.eval a c2219 := derived2219 a h
  have h5 : Entails.eval a c2302 := derived2302 a h
  have h6 : Entails.eval a c2296 := derived2296 a h
  have h7 : Entails.eval a c2086 := derived2086 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c2297 := derived2297 a h
  have h11 : Entails.eval a c2144 := derived2144 a h
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c1100 := derived1100 a h
  have h15 : Entails.eval a c2091 := derived2091 a h
  have h16 : Entails.eval a c2093 := derived2093 a h
  have h17 : Entails.eval a c2092 := derived2092 a h
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c2110 := derived2110 a h
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c2084 := derived2084 a h
  have h22 : Entails.eval a c2245 := derived2245 a h
  have h23 : Entails.eval a c68 := h 67 (by decide)
  have h24 : Entails.eval a c2137 := derived2137 a h
  have h25 : Entails.eval a c187 := h 186 (by decide)
  have h26 : Entails.eval a c2105 := derived2105 a h
  have h27 : Entails.eval a c185 := h 184 (by decide)
  have h28 : Entails.eval a c154 := h 153 (by decide)
  have h29 : Entails.eval a c27 := h 26 (by decide)
  have h30 : Entails.eval a c352 := h 351 (by decide)
  have h31 : Entails.eval a c2119 := derived2119 a h
  have h32 : Entails.eval a c102 := h 101 (by decide)
  have h33 : Entails.eval a c2041 := derived2041 a h
  have h34 : Entails.eval a c56 := h 55 (by decide)
  have h35 : Entails.eval a c342 := h 341 (by decide)
  have h36 : Entails.eval a c341 := h 340 (by decide)
  have h37 : Entails.eval a c245 := h 244 (by decide)
  have h38 : Entails.eval a c210 := h 209 (by decide)
  have h39 : Entails.eval a c303 := h 302 (by decide)
  have h40 : Entails.eval a c313 := h 312 (by decide)
  have h41 : Entails.eval a c143 := h 142 (by decide)
  have h42 : Entails.eval a c133 := h 132 (by decide)
  have h43 : Entails.eval a c229 := h 228 (by decide)
  have h44 : Entails.eval a c321 := h 320 (by decide)
  have h45 : Entails.eval a c179 := h 178 (by decide)
  have h46 : Entails.eval a c359 := h 358 (by decide)
  have h47 : Entails.eval a c368 := h 367 (by decide)
  have h48 : Entails.eval a c85 := h 84 (by decide)
  have h49 : Entails.eval a c289 := h 288 (by decide)
  have h50 : Entails.eval a c2128 := derived2128 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2304 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2295, some c2293, some c2294, some c2219, some c2292, some c2296, some c2086, some c2302, some c2303, some c2096, some c199, some c2100, some c2091, some c2090, some c1100, some c2141, some c154, some c350, some c2081, some c2084, some c182, some c245, some c183, some c2142, some c102, some c104, some c112, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p2304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2304 : lratChecker f2304 p2304 = .success := by decide +kernel
theorem unsat2304 : Unsatisfiable (PosFin 57) f2304 := by
  apply lratCheckerSound f2304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2304
  · intro a ha; simp [p2304] at ha; subst a; trivial
  · exact checked2304
theorem derived2304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2304 := by
  apply localUnsat_implies_entails f2304 [c2295, c2293, c2294, c2219, c2292, c2296, c2086, c2302, c2303, c2096, c199, c2100, c2091, c2090, c1100, c2141, c154, c350, c2081, c2084, c182, c245, c183, c2142, c102, c104, c112] c2304 unsat2304 (by rfl) a
  have h0 : Entails.eval a c2295 := derived2295 a h
  have h1 : Entails.eval a c2293 := derived2293 a h
  have h2 : Entails.eval a c2294 := derived2294 a h
  have h3 : Entails.eval a c2219 := derived2219 a h
  have h4 : Entails.eval a c2292 := derived2292 a h
  have h5 : Entails.eval a c2296 := derived2296 a h
  have h6 : Entails.eval a c2086 := derived2086 a h
  have h7 : Entails.eval a c2302 := derived2302 a h
  have h8 : Entails.eval a c2303 := derived2303 a h
  have h9 : Entails.eval a c2096 := derived2096 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c2100 := derived2100 a h
  have h12 : Entails.eval a c2091 := derived2091 a h
  have h13 : Entails.eval a c2090 := derived2090 a h
  have h14 : Entails.eval a c1100 := derived1100 a h
  have h15 : Entails.eval a c2141 := derived2141 a h
  have h16 : Entails.eval a c154 := h 153 (by decide)
  have h17 : Entails.eval a c350 := h 349 (by decide)
  have h18 : Entails.eval a c2081 := derived2081 a h
  have h19 : Entails.eval a c2084 := derived2084 a h
  have h20 : Entails.eval a c182 := h 181 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c183 := h 182 (by decide)
  have h23 : Entails.eval a c2142 := derived2142 a h
  have h24 : Entails.eval a c102 := h 101 (by decide)
  have h25 : Entails.eval a c104 := h 103 (by decide)
  have h26 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2305 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2304, some c2219, some c1967, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p2305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2305 : lratChecker f2305 p2305 = .success := by decide +kernel
theorem unsat2305 : Unsatisfiable (PosFin 57) f2305 := by
  apply lratCheckerSound f2305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2305
  · intro a ha; simp [p2305] at ha; subst a; trivial
  · exact checked2305
theorem derived2305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2305 := by
  apply localUnsat_implies_entails f2305 [c2304, c2219, c1967] c2305 unsat2305 (by rfl) a
  have h0 : Entails.eval a c2304 := derived2304 a h
  have h1 : Entails.eval a c2219 := derived2219 a h
  have h2 : Entails.eval a c1967 := derived1967 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2306 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2305, some c2295, some c2292, some c2219, some c2304, some c2293, some c2294, some c2094, some c1254, some c26, some c228, some c2138, some c2124, some c2100, some c155, some c2081, some c2082, some c182, some c245, some c353, some c343, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2306 : lratChecker f2306 p2306 = .success := by decide +kernel
theorem unsat2306 : Unsatisfiable (PosFin 57) f2306 := by
  apply lratCheckerSound f2306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2306
  · intro a ha; simp [p2306] at ha; subst a; trivial
  · exact checked2306
theorem derived2306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2306 := by
  apply localUnsat_implies_entails f2306 [c2305, c2295, c2292, c2219, c2304, c2293, c2294, c2094, c1254, c26, c228, c2138, c2124, c2100, c155, c2081, c2082, c182, c245, c353, c343] c2306 unsat2306 (by rfl) a
  have h0 : Entails.eval a c2305 := derived2305 a h
  have h1 : Entails.eval a c2295 := derived2295 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c2219 := derived2219 a h
  have h4 : Entails.eval a c2304 := derived2304 a h
  have h5 : Entails.eval a c2293 := derived2293 a h
  have h6 : Entails.eval a c2294 := derived2294 a h
  have h7 : Entails.eval a c2094 := derived2094 a h
  have h8 : Entails.eval a c1254 := derived1254 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c2138 := derived2138 a h
  have h12 : Entails.eval a c2124 := derived2124 a h
  have h13 : Entails.eval a c2100 := derived2100 a h
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c2081 := derived2081 a h
  have h16 : Entails.eval a c2082 := derived2082 a h
  have h17 : Entails.eval a c182 := h 181 (by decide)
  have h18 : Entails.eval a c245 := h 244 (by decide)
  have h19 : Entails.eval a c353 := h 352 (by decide)
  have h20 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2307 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2306, some c2086, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2307 : lratChecker f2307 p2307 = .success := by decide +kernel
theorem unsat2307 : Unsatisfiable (PosFin 57) f2307 := by
  apply lratCheckerSound f2307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2307
  · intro a ha; simp [p2307] at ha; subst a; trivial
  · exact checked2307
theorem derived2307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2307 := by
  apply localUnsat_implies_entails f2307 [c2306, c2086] c2307 unsat2307 (by rfl) a
  have h0 : Entails.eval a c2306 := derived2306 a h
  have h1 : Entails.eval a c2086 := derived2086 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2308 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2307, some c2304, some c2101, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p2308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2308 : lratChecker f2308 p2308 = .success := by decide +kernel
theorem unsat2308 : Unsatisfiable (PosFin 57) f2308 := by
  apply lratCheckerSound f2308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2308
  · intro a ha; simp [p2308] at ha; subst a; trivial
  · exact checked2308
theorem derived2308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2308 := by
  apply localUnsat_implies_entails f2308 [c2307, c2304, c2101] c2308 unsat2308 (by rfl) a
  have h0 : Entails.eval a c2307 := derived2307 a h
  have h1 : Entails.eval a c2304 := derived2304 a h
  have h2 : Entails.eval a c2101 := derived2101 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2309 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2307, some c2304, some c3, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p2309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2309 : lratChecker f2309 p2309 = .success := by decide +kernel
theorem unsat2309 : Unsatisfiable (PosFin 57) f2309 := by
  apply lratCheckerSound f2309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2309
  · intro a ha; simp [p2309] at ha; subst a; trivial
  · exact checked2309
theorem derived2309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2309 := by
  apply localUnsat_implies_entails f2309 [c2307, c2304, c3] c2309 unsat2309 (by rfl) a
  have h0 : Entails.eval a c2307 := derived2307 a h
  have h1 : Entails.eval a c2304 := derived2304 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2310 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2307, some c2304, some c23, some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p2310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2310 : lratChecker f2310 p2310 = .success := by decide +kernel
theorem unsat2310 : Unsatisfiable (PosFin 57) f2310 := by
  apply lratCheckerSound f2310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2310
  · intro a ha; simp [p2310] at ha; subst a; trivial
  · exact checked2310
theorem derived2310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2310 := by
  apply localUnsat_implies_entails f2310 [c2307, c2304, c23] c2310 unsat2310 (by rfl) a
  have h0 : Entails.eval a c2307 := derived2307 a h
  have h1 : Entails.eval a c2304 := derived2304 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2311 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2307, some c2304, some c2292, some c34, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2311 : lratChecker f2311 p2311 = .success := by decide +kernel
theorem unsat2311 : Unsatisfiable (PosFin 57) f2311 := by
  apply lratCheckerSound f2311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2311
  · intro a ha; simp [p2311] at ha; subst a; trivial
  · exact checked2311
theorem derived2311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2311 := by
  apply localUnsat_implies_entails f2311 [c2307, c2304, c2292, c34] c2311 unsat2311 (by rfl) a
  have h0 : Entails.eval a c2307 := derived2307 a h
  have h1 : Entails.eval a c2304 := derived2304 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2312 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2309, some c2307, some c2219, some c2292, some c2295, some c1100, some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p2312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2312 : lratChecker f2312 p2312 = .success := by decide +kernel
theorem unsat2312 : Unsatisfiable (PosFin 57) f2312 := by
  apply lratCheckerSound f2312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2312
  · intro a ha; simp [p2312] at ha; subst a; trivial
  · exact checked2312
theorem derived2312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2312 := by
  apply localUnsat_implies_entails f2312 [c2309, c2307, c2219, c2292, c2295, c1100] c2312 unsat2312 (by rfl) a
  have h0 : Entails.eval a c2309 := derived2309 a h
  have h1 : Entails.eval a c2307 := derived2307 a h
  have h2 : Entails.eval a c2219 := derived2219 a h
  have h3 : Entails.eval a c2292 := derived2292 a h
  have h4 : Entails.eval a c2295 := derived2295 a h
  have h5 : Entails.eval a c1100 := derived1100 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2313 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2310, some c2219, some c2309, some c163, some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p2313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2313 : lratChecker f2313 p2313 = .success := by decide +kernel
theorem unsat2313 : Unsatisfiable (PosFin 57) f2313 := by
  apply lratCheckerSound f2313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2313
  · intro a ha; simp [p2313] at ha; subst a; trivial
  · exact checked2313
theorem derived2313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2313 := by
  apply localUnsat_implies_entails f2313 [c2310, c2219, c2309, c163] c2313 unsat2313 (by rfl) a
  have h0 : Entails.eval a c2310 := derived2310 a h
  have h1 : Entails.eval a c2219 := derived2219 a h
  have h2 : Entails.eval a c2309 := derived2309 a h
  have h3 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2313

end CochromaticTwenty.Certificates.B16_0_2Enumerating
