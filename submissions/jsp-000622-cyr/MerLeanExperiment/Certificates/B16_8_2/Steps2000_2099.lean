import MerLeanExperiment.Certificates.B16_8_2.Steps1900_1999

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2381 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2036, some c2345, some c2151, some c2375, some c2376, some c2377, some c2167, some c2094, some c2380, some c379, some c152, some c2296, some c6, some c167, some c173, some c169, some c183, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2381 : lratChecker f2381 p2381 = .success := by decide +kernel
theorem unsat2381 : Unsatisfiable (PosFin 57) f2381 := by
  apply lratCheckerSound f2381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2381
  · intro a ha; simp [p2381] at ha; subst a; trivial
  · exact checked2381
theorem derived2381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2381 := by
  apply localUnsat_implies_entails f2381 [c2364, c100, c2036, c2345, c2151, c2375, c2376, c2377, c2167, c2094, c2380, c379, c152, c2296, c6, c167, c173, c169, c183] c2381 unsat2381 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2036 := derived2036 a h
  have h3 : Entails.eval a c2345 := derived2345 a h
  have h4 : Entails.eval a c2151 := derived2151 a h
  have h5 : Entails.eval a c2375 := derived2375 a h
  have h6 : Entails.eval a c2376 := derived2376 a h
  have h7 : Entails.eval a c2377 := derived2377 a h
  have h8 : Entails.eval a c2167 := derived2167 a h
  have h9 : Entails.eval a c2094 := derived2094 a h
  have h10 : Entails.eval a c2380 := derived2380 a h
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c2296 := derived2296 a h
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2382 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c6, some c8, some c165, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2382 : lratChecker f2382 p2382 = .success := by decide +kernel
theorem unsat2382 : Unsatisfiable (PosFin 57) f2382 := by
  apply lratCheckerSound f2382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2382
  · intro a ha; simp [p2382] at ha; subst a; trivial
  · exact checked2382
theorem derived2382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2382 := by
  apply localUnsat_implies_entails f2382 [c2364, c6, c8, c165] c2382 unsat2382 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2383 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2382, some c2376, some c2364, some c100, some c2171, some c172, some c2167, some c2260, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2383 : lratChecker f2383 p2383 = .success := by decide +kernel
theorem unsat2383 : Unsatisfiable (PosFin 57) f2383 := by
  apply lratCheckerSound f2383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2383
  · intro a ha; simp [p2383] at ha; subst a; trivial
  · exact checked2383
theorem derived2383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2383 := by
  apply localUnsat_implies_entails f2383 [c2382, c2376, c2364, c100, c2171, c172, c2167, c2260] c2383 unsat2383 (by rfl) a
  have h0 : Entails.eval a c2382 := derived2382 a h
  have h1 : Entails.eval a c2376 := derived2376 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2171 := derived2171 a h
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c2167 := derived2167 a h
  have h7 : Entails.eval a c2260 := derived2260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2384 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c100, some c2036, some c2345, some c2151, some c2375, some c2376, some c2381, some c79, some c2382, some c2383, some c2230, some c379, some c2365, some c173, some c2296, some c2167, some c16, some c167, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2384 : lratChecker f2384 p2384 = .success := by decide +kernel
theorem unsat2384 : Unsatisfiable (PosFin 57) f2384 := by
  apply lratCheckerSound f2384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2384
  · intro a ha; simp [p2384] at ha; subst a; trivial
  · exact checked2384
theorem derived2384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2384 := by
  apply localUnsat_implies_entails f2384 [c2201, c2364, c100, c2036, c2345, c2151, c2375, c2376, c2381, c79, c2382, c2383, c2230, c379, c2365, c173, c2296, c2167, c16, c167] c2384 unsat2384 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2036 := derived2036 a h
  have h4 : Entails.eval a c2345 := derived2345 a h
  have h5 : Entails.eval a c2151 := derived2151 a h
  have h6 : Entails.eval a c2375 := derived2375 a h
  have h7 : Entails.eval a c2376 := derived2376 a h
  have h8 : Entails.eval a c2381 := derived2381 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c2382 := derived2382 a h
  have h11 : Entails.eval a c2383 := derived2383 a h
  have h12 : Entails.eval a c2230 := derived2230 a h
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c2365 := derived2365 a h
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c2296 := derived2296 a h
  have h17 : Entails.eval a c2167 := derived2167 a h
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2385 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c69, some c2167, some c2036, some c2345, some c78, some c79, some c2382, some c172, some c1491, some c163, some c2089, some c38, some c62, some c2031, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2385 : lratChecker f2385 p2385 = .success := by decide +kernel
theorem unsat2385 : Unsatisfiable (PosFin 57) f2385 := by
  apply lratCheckerSound f2385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2385
  · intro a ha; simp [p2385] at ha; subst a; trivial
  · exact checked2385
theorem derived2385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2385 := by
  apply localUnsat_implies_entails f2385 [c2364, c100, c69, c2167, c2036, c2345, c78, c79, c2382, c172, c1491, c163, c2089, c38, c62, c2031] c2385 unsat2385 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c2167 := derived2167 a h
  have h4 : Entails.eval a c2036 := derived2036 a h
  have h5 : Entails.eval a c2345 := derived2345 a h
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c2382 := derived2382 a h
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c1491 := derived1491 a h
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c2089 := derived2089 a h
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c2031 := derived2031 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2386 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2364, some c100, some c2151, some c69, some c2385, some c2373, some c282, some c1014, some c37, some c2026, some c313, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2386 : lratChecker f2386 p2386 = .success := by decide +kernel
theorem unsat2386 : Unsatisfiable (PosFin 57) f2386 := by
  apply lratCheckerSound f2386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2386
  · intro a ha; simp [p2386] at ha; subst a; trivial
  · exact checked2386
theorem derived2386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2386 := by
  apply localUnsat_implies_entails f2386 [c2345, c2364, c100, c2151, c69, c2385, c2373, c282, c1014, c37, c2026, c313] c2386 unsat2386 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c2385 := derived2385 a h
  have h6 : Entails.eval a c2373 := derived2373 a h
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c1014 := derived1014 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c2026 := derived2026 a h
  have h11 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2387 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2364, some c100, some c2151, some c2375, some c2376, some c2036, some c2384, some c2386, some c1543, some c2365, some c1524, some c2062, some c58, some c62, some c338, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2387 : lratChecker f2387 p2387 = .success := by decide +kernel
theorem unsat2387 : Unsatisfiable (PosFin 57) f2387 := by
  apply lratCheckerSound f2387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2387
  · intro a ha; simp [p2387] at ha; subst a; trivial
  · exact checked2387
theorem derived2387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2387 := by
  apply localUnsat_implies_entails f2387 [c2345, c2364, c100, c2151, c2375, c2376, c2036, c2384, c2386, c1543, c2365, c1524, c2062, c58, c62, c338] c2387 unsat2387 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c2375 := derived2375 a h
  have h5 : Entails.eval a c2376 := derived2376 a h
  have h6 : Entails.eval a c2036 := derived2036 a h
  have h7 : Entails.eval a c2384 := derived2384 a h
  have h8 : Entails.eval a c2386 := derived2386 a h
  have h9 : Entails.eval a c1543 := derived1543 a h
  have h10 : Entails.eval a c2365 := derived2365 a h
  have h11 : Entails.eval a c1524 := derived1524 a h
  have h12 : Entails.eval a c2062 := derived2062 a h
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2388 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2364, some c100, some c2151, some c2375, some c2376, some c2387, some c2048, some c2045, some c374, some c72, some c1051, some c361, some c2382, some c173, some c2230, some c2094, some c2383, some c2021, some c2043, some c67, some c352, some c351, some c297, some c299, some c268, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2388 : lratChecker f2388 p2388 = .success := by decide +kernel
theorem unsat2388 : Unsatisfiable (PosFin 57) f2388 := by
  apply lratCheckerSound f2388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2388
  · intro a ha; simp [p2388] at ha; subst a; trivial
  · exact checked2388
theorem derived2388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2388 := by
  apply localUnsat_implies_entails f2388 [c2201, c2345, c2364, c100, c2151, c2375, c2376, c2387, c2048, c2045, c374, c72, c1051, c361, c2382, c173, c2230, c2094, c2383, c2021, c2043, c67, c352, c351, c297, c299, c268] c2388 unsat2388 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2151 := derived2151 a h
  have h5 : Entails.eval a c2375 := derived2375 a h
  have h6 : Entails.eval a c2376 := derived2376 a h
  have h7 : Entails.eval a c2387 := derived2387 a h
  have h8 : Entails.eval a c2048 := derived2048 a h
  have h9 : Entails.eval a c2045 := derived2045 a h
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c1051 := derived1051 a h
  have h13 : Entails.eval a c361 := h 360 (by decide)
  have h14 : Entails.eval a c2382 := derived2382 a h
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c2230 := derived2230 a h
  have h17 : Entails.eval a c2094 := derived2094 a h
  have h18 : Entails.eval a c2383 := derived2383 a h
  have h19 : Entails.eval a c2021 := derived2021 a h
  have h20 : Entails.eval a c2043 := derived2043 a h
  have h21 : Entails.eval a c67 := h 66 (by decide)
  have h22 : Entails.eval a c352 := h 351 (by decide)
  have h23 : Entails.eval a c351 := h 350 (by decide)
  have h24 : Entails.eval a c297 := h 296 (by decide)
  have h25 : Entails.eval a c299 := h 298 (by decide)
  have h26 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2389 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨26, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c323, some c283, some c265, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p2389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2389 : lratChecker f2389 p2389 = .success := by decide +kernel
theorem unsat2389 : Unsatisfiable (PosFin 57) f2389 := by
  apply lratCheckerSound f2389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2389
  · intro a ha; simp [p2389] at ha; subst a; trivial
  · exact checked2389
theorem derived2389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2389 := by
  apply localUnsat_implies_entails f2389 [c323, c283, c265] c2389 unsat2389 (by rfl) a
  have h0 : Entails.eval a c323 := h 322 (by decide)
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2390 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨26, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨44, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2230, some c2365, some c155, some c1118, some c143, some c127, some c265, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2390 : lratChecker f2390 p2390 = .success := by decide +kernel
theorem unsat2390 : Unsatisfiable (PosFin 57) f2390 := by
  apply lratCheckerSound f2390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2390
  · intro a ha; simp [p2390] at ha; subst a; trivial
  · exact checked2390
theorem derived2390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2390 := by
  apply localUnsat_implies_entails f2390 [c2230, c2365, c155, c1118, c143, c127, c265] c2390 unsat2390 (by rfl) a
  have h0 : Entails.eval a c2230 := derived2230 a h
  have h1 : Entails.eval a c2365 := derived2365 a h
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2391 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2151, some c2388, some c2035, some c2027, some c2048, some c2045, some c317, some c1014, some c277, some c2389, some c2390, some c69, some c153, some c2260, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2391 : lratChecker f2391 p2391 = .success := by decide +kernel
theorem unsat2391 : Unsatisfiable (PosFin 57) f2391 := by
  apply lratCheckerSound f2391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2391
  · intro a ha; simp [p2391] at ha; subst a; trivial
  · exact checked2391
theorem derived2391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2391 := by
  apply localUnsat_implies_entails f2391 [c2364, c100, c2345, c2151, c2388, c2035, c2027, c2048, c2045, c317, c1014, c277, c2389, c2390, c69, c153, c2260] c2391 unsat2391 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c2388 := derived2388 a h
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c2048 := derived2048 a h
  have h8 : Entails.eval a c2045 := derived2045 a h
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c1014 := derived1014 a h
  have h11 : Entails.eval a c277 := h 276 (by decide)
  have h12 : Entails.eval a c2389 := derived2389 a h
  have h13 : Entails.eval a c2390 := derived2390 a h
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c2260 := derived2260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2392 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2035, some c2364, some c100, some c2345, some c367, some c366, some c78, some c371, some c1287, some c153, some c378, some c377, some c12, some c1986, some c171, some c983, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2392 : lratChecker f2392 p2392 = .success := by decide +kernel
theorem unsat2392 : Unsatisfiable (PosFin 57) f2392 := by
  apply lratCheckerSound f2392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2392
  · intro a ha; simp [p2392] at ha; subst a; trivial
  · exact checked2392
theorem derived2392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2392 := by
  apply localUnsat_implies_entails f2392 [c2035, c2364, c100, c2345, c367, c366, c78, c371, c1287, c153, c378, c377, c12, c1986, c171, c983] c2392 unsat2392 (by rfl) a
  have h0 : Entails.eval a c2035 := derived2035 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2345 := derived2345 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c1986 := derived1986 a h
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c983 := derived983 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2393 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c363, some c378, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2393 : lratChecker f2393 p2393 = .success := by decide +kernel
theorem unsat2393 : Unsatisfiable (PosFin 57) f2393 := by
  apply lratCheckerSound f2393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2393
  · intro a ha; simp [p2393] at ha; subst a; trivial
  · exact checked2393
theorem derived2393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2393 := by
  apply localUnsat_implies_entails f2393 [c356, c363, c378] c2393 unsat2393 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2394 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c1142, some c841, some c156, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p2394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2394 : lratChecker f2394 p2394 = .success := by decide +kernel
theorem unsat2394 : Unsatisfiable (PosFin 57) f2394 := by
  apply lratCheckerSound f2394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2394
  · intro a ha; simp [p2394] at ha; subst a; trivial
  · exact checked2394
theorem derived2394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2394 := by
  apply localUnsat_implies_entails f2394 [c357, c1142, c841, c156] c2394 unsat2394 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c1142 := derived1142 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2395 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2391, some c2364, some c100, some c2392, some c2393, some c2167, some c371, some c79, some c2394, some c378, some c156, some c1051, some c8, some c161, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2395 : lratChecker f2395 p2395 = .success := by decide +kernel
theorem unsat2395 : Unsatisfiable (PosFin 57) f2395 := by
  apply lratCheckerSound f2395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2395
  · intro a ha; simp [p2395] at ha; subst a; trivial
  · exact checked2395
theorem derived2395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2395 := by
  apply localUnsat_implies_entails f2395 [c2201, c2391, c2364, c100, c2392, c2393, c2167, c371, c79, c2394, c378, c156, c1051, c8, c161] c2395 unsat2395 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2391 := derived2391 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2392 := derived2392 a h
  have h5 : Entails.eval a c2393 := derived2393 a h
  have h6 : Entails.eval a c2167 := derived2167 a h
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c2394 := derived2394 a h
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c1051 := derived1051 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2396 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2391, some c2364, some c100, some c2345, some c367, some c366, some c357, some c78, some c378, some c371, some c1245, some c166, some c6, some c186, some c177, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2396 : lratChecker f2396 p2396 = .success := by decide +kernel
theorem unsat2396 : Unsatisfiable (PosFin 57) f2396 := by
  apply lratCheckerSound f2396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2396
  · intro a ha; simp [p2396] at ha; subst a; trivial
  · exact checked2396
theorem derived2396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2396 := by
  apply localUnsat_implies_entails f2396 [c2391, c2364, c100, c2345, c367, c366, c357, c78, c378, c371, c1245, c166, c6, c186, c177] c2396 unsat2396 (by rfl) a
  have h0 : Entails.eval a c2391 := derived2391 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2345 := derived2345 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c1245 := derived1245 a h
  have h11 : Entails.eval a c166 := h 165 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c186 := h 185 (by decide)
  have h14 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2397 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c160, some c167, some c6, some c176, some c171, some c183, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2397 : lratChecker f2397 p2397 = .success := by decide +kernel
theorem unsat2397 : Unsatisfiable (PosFin 57) f2397 := by
  apply lratCheckerSound f2397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2397
  · intro a ha; simp [p2397] at ha; subst a; trivial
  · exact checked2397
theorem derived2397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2397 := by
  apply localUnsat_implies_entails f2397 [c2364, c160, c167, c6, c176, c171, c183] c2397 unsat2397 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2398 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c100, some c2036, some c2035, some c2391, some c2395, some c2230, some c379, some c2296, some c2396, some c2397, some c2167, some c155, some c357, some c1051, some c378, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2398 : lratChecker f2398 p2398 = .success := by decide +kernel
theorem unsat2398 : Unsatisfiable (PosFin 57) f2398 := by
  apply lratCheckerSound f2398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2398
  · intro a ha; simp [p2398] at ha; subst a; trivial
  · exact checked2398
theorem derived2398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2398 := by
  apply localUnsat_implies_entails f2398 [c2201, c2364, c100, c2036, c2035, c2391, c2395, c2230, c379, c2296, c2396, c2397, c2167, c155, c357, c1051, c378] c2398 unsat2398 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2036 := derived2036 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2391 := derived2391 a h
  have h6 : Entails.eval a c2395 := derived2395 a h
  have h7 : Entails.eval a c2230 := derived2230 a h
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c2296 := derived2296 a h
  have h10 : Entails.eval a c2396 := derived2396 a h
  have h11 : Entails.eval a c2397 := derived2397 a h
  have h12 : Entails.eval a c2167 := derived2167 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c1051 := derived1051 a h
  have h16 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2399 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2026, some c59, some c316, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2399 : lratChecker f2399 p2399 = .success := by decide +kernel
theorem unsat2399 : Unsatisfiable (PosFin 57) f2399 := by
  apply lratCheckerSound f2399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2399
  · intro a ha; simp [p2399] at ha; subst a; trivial
  · exact checked2399
theorem derived2399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2399 := by
  apply localUnsat_implies_entails f2399 [c2026, c59, c316] c2399 unsat2399 (by rfl) a
  have h0 : Entails.eval a c2026 := derived2026 a h
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2400 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2398, some c2035, some c367, some c2260, some c153, some c2364, some c100, some c2345, some c366, some c78, some c2391, some c1660, some c2036, some c357, some c150, some c841, some c6, some c179, some c152, some c8, some c2399, some c339, some c337, some c2367, some c1194, some c276, some c132, some c2039, some c268, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2400 : lratChecker f2400 p2400 = .success := by decide +kernel
theorem unsat2400 : Unsatisfiable (PosFin 57) f2400 := by
  apply lratCheckerSound f2400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2400
  · intro a ha; simp [p2400] at ha; subst a; trivial
  · exact checked2400
theorem derived2400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2400 := by
  apply localUnsat_implies_entails f2400 [c2398, c2035, c367, c2260, c153, c2364, c100, c2345, c366, c78, c2391, c1660, c2036, c357, c150, c841, c6, c179, c152, c8, c2399, c339, c337, c2367, c1194, c276, c132, c2039, c268] c2400 unsat2400 (by rfl) a
  have h0 : Entails.eval a c2398 := derived2398 a h
  have h1 : Entails.eval a c2035 := derived2035 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2260 := derived2260 a h
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c2364 := derived2364 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c2345 := derived2345 a h
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c2391 := derived2391 a h
  have h11 : Entails.eval a c1660 := derived1660 a h
  have h12 : Entails.eval a c2036 := derived2036 a h
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c179 := h 178 (by decide)
  have h18 : Entails.eval a c152 := h 151 (by decide)
  have h19 : Entails.eval a c8 := h 7 (by decide)
  have h20 : Entails.eval a c2399 := derived2399 a h
  have h21 : Entails.eval a c339 := h 338 (by decide)
  have h22 : Entails.eval a c337 := h 336 (by decide)
  have h23 : Entails.eval a c2367 := derived2367 a h
  have h24 : Entails.eval a c1194 := derived1194 a h
  have h25 : Entails.eval a c276 := h 275 (by decide)
  have h26 : Entails.eval a c132 := h 131 (by decide)
  have h27 : Entails.eval a c2039 := derived2039 a h
  have h28 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2401 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨39, by decide⟩, true), (⟨55, by decide⟩, false), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c299, some c265, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p2401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2401 : lratChecker f2401 p2401 = .success := by decide +kernel
theorem unsat2401 : Unsatisfiable (PosFin 57) f2401 := by
  apply lratCheckerSound f2401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2401
  · intro a ha; simp [p2401] at ha; subst a; trivial
  · exact checked2401
theorem derived2401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2401 := by
  apply localUnsat_implies_entails f2401 [c293, c299, c265] c2401 unsat2401 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2402 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2398, some c2364, some c100, some c2036, some c2035, some c2391, some c2345, some c367, some c2260, some c1660, some c2400, some c1688, some c378, some c377, some c179, some c360, some c16, some c2399, some c339, some c2401, some c2047, some c47, some c276, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2402 : lratChecker f2402 p2402 = .success := by decide +kernel
theorem unsat2402 : Unsatisfiable (PosFin 57) f2402 := by
  apply lratCheckerSound f2402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2402
  · intro a ha; simp [p2402] at ha; subst a; trivial
  · exact checked2402
theorem derived2402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2402 := by
  apply localUnsat_implies_entails f2402 [c2201, c2398, c2364, c100, c2036, c2035, c2391, c2345, c367, c2260, c1660, c2400, c1688, c378, c377, c179, c360, c16, c2399, c339, c2401, c2047, c47, c276] c2402 unsat2402 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2398 := derived2398 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2036 := derived2036 a h
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2391 := derived2391 a h
  have h7 : Entails.eval a c2345 := derived2345 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c2260 := derived2260 a h
  have h10 : Entails.eval a c1660 := derived1660 a h
  have h11 : Entails.eval a c2400 := derived2400 a h
  have h12 : Entails.eval a c1688 := derived1688 a h
  have h13 : Entails.eval a c378 := h 377 (by decide)
  have h14 : Entails.eval a c377 := h 376 (by decide)
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c2399 := derived2399 a h
  have h19 : Entails.eval a c339 := h 338 (by decide)
  have h20 : Entails.eval a c2401 := derived2401 a h
  have h21 : Entails.eval a c2047 := derived2047 a h
  have h22 : Entails.eval a c47 := h 46 (by decide)
  have h23 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2403 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2398, some c2391, some c2364, some c100, some c2402, some c2376, some c2383, some c2393, some c72, some c2167, some c841, some c357, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2403 : lratChecker f2403 p2403 = .success := by decide +kernel
theorem unsat2403 : Unsatisfiable (PosFin 57) f2403 := by
  apply lratCheckerSound f2403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2403
  · intro a ha; simp [p2403] at ha; subst a; trivial
  · exact checked2403
theorem derived2403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2403 := by
  apply localUnsat_implies_entails f2403 [c2398, c2391, c2364, c100, c2402, c2376, c2383, c2393, c72, c2167, c841, c357] c2403 unsat2403 (by rfl) a
  have h0 : Entails.eval a c2398 := derived2398 a h
  have h1 : Entails.eval a c2391 := derived2391 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2402 := derived2402 a h
  have h5 : Entails.eval a c2376 := derived2376 a h
  have h6 : Entails.eval a c2383 := derived2383 a h
  have h7 : Entails.eval a c2393 := derived2393 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c2167 := derived2167 a h
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2404 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2036, some c2035, some c2391, some c2398, some c2403, some c2230, some c2365, some c379, some c2296, some c367, some c2167, some c2397, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2404 : lratChecker f2404 p2404 = .success := by decide +kernel
theorem unsat2404 : Unsatisfiable (PosFin 57) f2404 := by
  apply lratCheckerSound f2404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2404
  · intro a ha; simp [p2404] at ha; subst a; trivial
  · exact checked2404
theorem derived2404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2404 := by
  apply localUnsat_implies_entails f2404 [c2364, c100, c2036, c2035, c2391, c2398, c2403, c2230, c2365, c379, c2296, c367, c2167, c2397] c2404 unsat2404 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2036 := derived2036 a h
  have h3 : Entails.eval a c2035 := derived2035 a h
  have h4 : Entails.eval a c2391 := derived2391 a h
  have h5 : Entails.eval a c2398 := derived2398 a h
  have h6 : Entails.eval a c2403 := derived2403 a h
  have h7 : Entails.eval a c2230 := derived2230 a h
  have h8 : Entails.eval a c2365 := derived2365 a h
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c2296 := derived2296 a h
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c2167 := derived2167 a h
  have h13 : Entails.eval a c2397 := derived2397 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2405 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨47, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2404, some c2035, some c2391, some c2364, some c100, some c2345, some c78, some c366, some c1675, some c2394, some c378, some c156, some c1051, some c8, some c161, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2405 : lratChecker f2405 p2405 = .success := by decide +kernel
theorem unsat2405 : Unsatisfiable (PosFin 57) f2405 := by
  apply lratCheckerSound f2405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2405
  · intro a ha; simp [p2405] at ha; subst a; trivial
  · exact checked2405
theorem derived2405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2405 := by
  apply localUnsat_implies_entails f2405 [c2201, c2404, c2035, c2391, c2364, c100, c2345, c78, c366, c1675, c2394, c378, c156, c1051, c8, c161] c2405 unsat2405 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2404 := derived2404 a h
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c2391 := derived2391 a h
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c2345 := derived2345 a h
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c1675 := derived1675 a h
  have h10 : Entails.eval a c2394 := derived2394 a h
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c156 := h 155 (by decide)
  have h13 : Entails.eval a c1051 := derived1051 a h
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2406 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2404, some c2035, some c2364, some c100, some c2167, some c2405, some c2373, some c282, some c37, some c2029, some c313, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2406 : lratChecker f2406 p2406 = .success := by decide +kernel
theorem unsat2406 : Unsatisfiable (PosFin 57) f2406 := by
  apply lratCheckerSound f2406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2406
  · intro a ha; simp [p2406] at ha; subst a; trivial
  · exact checked2406
theorem derived2406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2406 := by
  apply localUnsat_implies_entails f2406 [c2404, c2035, c2364, c100, c2167, c2405, c2373, c282, c37, c2029, c313] c2406 unsat2406 (by rfl) a
  have h0 : Entails.eval a c2404 := derived2404 a h
  have h1 : Entails.eval a c2035 := derived2035 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2167 := derived2167 a h
  have h5 : Entails.eval a c2405 := derived2405 a h
  have h6 : Entails.eval a c2373 := derived2373 a h
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c2029 := derived2029 a h
  have h10 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2407 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2035, some c2036, some c2404, some c2406, some c82, some c69, some c1543, some c2062, some c58, some c62, some c338, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2407 : lratChecker f2407 p2407 = .success := by decide +kernel
theorem unsat2407 : Unsatisfiable (PosFin 57) f2407 := by
  apply lratCheckerSound f2407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2407
  · intro a ha; simp [p2407] at ha; subst a; trivial
  · exact checked2407
theorem derived2407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2407 := by
  apply localUnsat_implies_entails f2407 [c2364, c100, c2345, c2035, c2036, c2404, c2406, c82, c69, c1543, c2062, c58, c62, c338] c2407 unsat2407 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2035 := derived2035 a h
  have h4 : Entails.eval a c2036 := derived2036 a h
  have h5 : Entails.eval a c2404 := derived2404 a h
  have h6 : Entails.eval a c2406 := derived2406 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c1543 := derived1543 a h
  have h10 : Entails.eval a c2062 := derived2062 a h
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2408 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨41, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2407, some c374, some c2391, some c2364, some c100, some c2345, some c367, some c366, some c78, some c371, some c1287, some c153, some c377, some c14, some c1986, some c161, some c168, some c186, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2408 : lratChecker f2408 p2408 = .success := by decide +kernel
theorem unsat2408 : Unsatisfiable (PosFin 57) f2408 := by
  apply lratCheckerSound f2408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2408
  · intro a ha; simp [p2408] at ha; subst a; trivial
  · exact checked2408
theorem derived2408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2408 := by
  apply localUnsat_implies_entails f2408 [c2201, c2407, c374, c2391, c2364, c100, c2345, c367, c366, c78, c371, c1287, c153, c377, c14, c1986, c161, c168, c186] c2408 unsat2408 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2407 := derived2407 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c2391 := derived2391 a h
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c2345 := derived2345 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c1287 := derived1287 a h
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c1986 := derived1986 a h
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c168 := h 167 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2409 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2407, some c374, some c2391, some c2364, some c100, some c2393, some c72, some c156, some c1051, some c2167, some c8, some c161, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2409 : lratChecker f2409 p2409 = .success := by decide +kernel
theorem unsat2409 : Unsatisfiable (PosFin 57) f2409 := by
  apply lratCheckerSound f2409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2409
  · intro a ha; simp [p2409] at ha; subst a; trivial
  · exact checked2409
theorem derived2409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2409 := by
  apply localUnsat_implies_entails f2409 [c2201, c2407, c374, c2391, c2364, c100, c2393, c72, c156, c1051, c2167, c8, c161] c2409 unsat2409 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2407 := derived2407 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c2391 := derived2391 a h
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c2393 := derived2393 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c1051 := derived1051 a h
  have h10 : Entails.eval a c2167 := derived2167 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2410 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2409, some c2407, some c374, some c2364, some c100, some c2345, some c2045, some c2048, some c2391, some c367, some c366, some c2408, some c78, some c2260, some c1660, some c153, some c1985, some c282, some c322, some c193, some c28, some c221, some c230, some c106, some c107, some c143, some c127, some c141, some c125, some c268, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2410 : lratChecker f2410 p2410 = .success := by decide +kernel
theorem unsat2410 : Unsatisfiable (PosFin 57) f2410 := by
  apply lratCheckerSound f2410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2410
  · intro a ha; simp [p2410] at ha; subst a; trivial
  · exact checked2410
theorem derived2410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2410 := by
  apply localUnsat_implies_entails f2410 [c2409, c2407, c374, c2364, c100, c2345, c2045, c2048, c2391, c367, c366, c2408, c78, c2260, c1660, c153, c1985, c282, c322, c193, c28, c221, c230, c106, c107, c143, c127, c141, c125, c268] c2410 unsat2410 (by rfl) a
  have h0 : Entails.eval a c2409 := derived2409 a h
  have h1 : Entails.eval a c2407 := derived2407 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c2364 := derived2364 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2345 := derived2345 a h
  have h6 : Entails.eval a c2045 := derived2045 a h
  have h7 : Entails.eval a c2048 := derived2048 a h
  have h8 : Entails.eval a c2391 := derived2391 a h
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c2408 := derived2408 a h
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c2260 := derived2260 a h
  have h14 : Entails.eval a c1660 := derived1660 a h
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c1985 := derived1985 a h
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c322 := h 321 (by decide)
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c221 := h 220 (by decide)
  have h22 : Entails.eval a c230 := h 229 (by decide)
  have h23 : Entails.eval a c106 := h 105 (by decide)
  have h24 : Entails.eval a c107 := h 106 (by decide)
  have h25 : Entails.eval a c143 := h 142 (by decide)
  have h26 : Entails.eval a c127 := h 126 (by decide)
  have h27 : Entails.eval a c141 := h 140 (by decide)
  have h28 : Entails.eval a c125 := h 124 (by decide)
  have h29 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2411 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2407, some c2045, some c2048, some c1688, some c339, some c2401, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2411 : lratChecker f2411 p2411 = .success := by decide +kernel
theorem unsat2411 : Unsatisfiable (PosFin 57) f2411 := by
  apply lratCheckerSound f2411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2411
  · intro a ha; simp [p2411] at ha; subst a; trivial
  · exact checked2411
theorem derived2411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2411 := by
  apply localUnsat_implies_entails f2411 [c2364, c100, c2345, c2407, c2045, c2048, c1688, c339, c2401] c2411 unsat2411 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2407 := derived2407 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c1688 := derived1688 a h
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c2401 := derived2401 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2412 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c100, some c2410, some c2027, some c2407, some c374, some c2345, some c2045, some c2048, some c2391, some c371, some c1287, some c281, some c321, some c153, some c377, some c14, some c2296, some c1986, some c2411, some c1010, some c8, some c161, some c323, some c283, some c268, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2412 : lratChecker f2412 p2412 = .success := by decide +kernel
theorem unsat2412 : Unsatisfiable (PosFin 57) f2412 := by
  apply lratCheckerSound f2412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2412
  · intro a ha; simp [p2412] at ha; subst a; trivial
  · exact checked2412
theorem derived2412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2412 := by
  apply localUnsat_implies_entails f2412 [c2201, c2364, c100, c2410, c2027, c2407, c374, c2345, c2045, c2048, c2391, c371, c1287, c281, c321, c153, c377, c14, c2296, c1986, c2411, c1010, c8, c161, c323, c283, c268] c2412 unsat2412 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2410 := derived2410 a h
  have h4 : Entails.eval a c2027 := derived2027 a h
  have h5 : Entails.eval a c2407 := derived2407 a h
  have h6 : Entails.eval a c374 := h 373 (by decide)
  have h7 : Entails.eval a c2345 := derived2345 a h
  have h8 : Entails.eval a c2045 := derived2045 a h
  have h9 : Entails.eval a c2048 := derived2048 a h
  have h10 : Entails.eval a c2391 := derived2391 a h
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c1287 := derived1287 a h
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c321 := h 320 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c377 := h 376 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c2296 := derived2296 a h
  have h19 : Entails.eval a c1986 := derived1986 a h
  have h20 : Entails.eval a c2411 := derived2411 a h
  have h21 : Entails.eval a c1010 := derived1010 a h
  have h22 : Entails.eval a c8 := h 7 (by decide)
  have h23 : Entails.eval a c161 := h 160 (by decide)
  have h24 : Entails.eval a c323 := h 322 (by decide)
  have h25 : Entails.eval a c283 := h 282 (by decide)
  have h26 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2413 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2412, some c2391, some c356, some c153, some c377, some c12, some c152, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2413 : lratChecker f2413 p2413 = .success := by decide +kernel
theorem unsat2413 : Unsatisfiable (PosFin 57) f2413 := by
  apply lratCheckerSound f2413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2413
  · intro a ha; simp [p2413] at ha; subst a; trivial
  · exact checked2413
theorem derived2413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2413 := by
  apply localUnsat_implies_entails f2413 [c2412, c2391, c356, c153, c377, c12, c152] c2413 unsat2413 (by rfl) a
  have h0 : Entails.eval a c2412 := derived2412 a h
  have h1 : Entails.eval a c2391 := derived2391 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2414 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2407, some c374, some c2391, some c2364, some c100, some c2410, some c2412, some c2413, some c2167, some c1665, some c1660, some c159, some c1985, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2414 : lratChecker f2414 p2414 = .success := by decide +kernel
theorem unsat2414 : Unsatisfiable (PosFin 57) f2414 := by
  apply lratCheckerSound f2414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2414
  · intro a ha; simp [p2414] at ha; subst a; trivial
  · exact checked2414
theorem derived2414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2414 := by
  apply localUnsat_implies_entails f2414 [c2407, c374, c2391, c2364, c100, c2410, c2412, c2413, c2167, c1665, c1660, c159, c1985] c2414 unsat2414 (by rfl) a
  have h0 : Entails.eval a c2407 := derived2407 a h
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c2391 := derived2391 a h
  have h3 : Entails.eval a c2364 := derived2364 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2410 := derived2410 a h
  have h6 : Entails.eval a c2412 := derived2412 a h
  have h7 : Entails.eval a c2413 := derived2413 a h
  have h8 : Entails.eval a c2167 := derived2167 a h
  have h9 : Entails.eval a c1665 := derived1665 a h
  have h10 : Entails.eval a c1660 := derived1660 a h
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c1985 := derived1985 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2415 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨48, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2027, some c78, some c366, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2415 : lratChecker f2415 p2415 = .success := by decide +kernel
theorem unsat2415 : Unsatisfiable (PosFin 57) f2415 := by
  apply lratCheckerSound f2415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2415
  · intro a ha; simp [p2415] at ha; subst a; trivial
  · exact checked2415
theorem derived2415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2415 := by
  apply localUnsat_implies_entails f2415 [c2364, c100, c2345, c2027, c78, c366] c2415 unsat2415 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2027 := derived2027 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2416 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2407, some c2045, some c2048, some c2409, some c2414, some c69, some c2415, some c282, some c322, some c37, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2416 : lratChecker f2416 p2416 = .success := by decide +kernel
theorem unsat2416 : Unsatisfiable (PosFin 57) f2416 := by
  apply lratCheckerSound f2416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2416
  · intro a ha; simp [p2416] at ha; subst a; trivial
  · exact checked2416
theorem derived2416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2416 := by
  apply localUnsat_implies_entails f2416 [c2364, c100, c2345, c2407, c2045, c2048, c2409, c2414, c69, c2415, c282, c322, c37] c2416 unsat2416 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2407 := derived2407 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c2409 := derived2409 a h
  have h7 : Entails.eval a c2414 := derived2414 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c2415 := derived2415 a h
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c322 := h 321 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2417 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨45, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2416, some c2230, some c2407, some c2345, some c2351, some c374, some c2391, some c72, some c156, some c1142, some c8, some c377, some c160, some c2296, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2417 : lratChecker f2417 p2417 = .success := by decide +kernel
theorem unsat2417 : Unsatisfiable (PosFin 57) f2417 := by
  apply lratCheckerSound f2417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2417
  · intro a ha; simp [p2417] at ha; subst a; trivial
  · exact checked2417
theorem derived2417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2417 := by
  apply localUnsat_implies_entails f2417 [c2364, c100, c2416, c2230, c2407, c2345, c2351, c374, c2391, c72, c156, c1142, c8, c377, c160, c2296] c2417 unsat2417 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2416 := derived2416 a h
  have h3 : Entails.eval a c2230 := derived2230 a h
  have h4 : Entails.eval a c2407 := derived2407 a h
  have h5 : Entails.eval a c2345 := derived2345 a h
  have h6 : Entails.eval a c2351 := derived2351 a h
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c2391 := derived2391 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c1142 := derived1142 a h
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c2296 := derived2296 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2418 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨21, by decide⟩, true), (⟨53, by decide⟩, false), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c298, some c338, some c193, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p2418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2418 : lratChecker f2418 p2418 = .success := by decide +kernel
theorem unsat2418 : Unsatisfiable (PosFin 57) f2418 := by
  apply lratCheckerSound f2418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2418
  · intro a ha; simp [p2418] at ha; subst a; trivial
  · exact checked2418
theorem derived2418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2418 := by
  apply localUnsat_implies_entails f2418 [c298, c338, c193] c2418 unsat2418 (by rfl) a
  have h0 : Entails.eval a c298 := h 297 (by decide)
  have h1 : Entails.eval a c338 := h 337 (by decide)
  have h2 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2419 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨51, by decide⟩, true), (⟨36, by decide⟩, true), (⟨28, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c155, some c1118, some c143, some c127, some c268, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p2419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2419 : lratChecker f2419 p2419 = .success := by decide +kernel
theorem unsat2419 : Unsatisfiable (PosFin 57) f2419 := by
  apply lratCheckerSound f2419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2419
  · intro a ha; simp [p2419] at ha; subst a; trivial
  · exact checked2419
theorem derived2419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2419 := by
  apply localUnsat_implies_entails f2419 [c155, c1118, c143, c127, c268] c2419 unsat2419 (by rfl) a
  have h0 : Entails.eval a c155 := h 154 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2420 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2416, some c2230, some c2407, some c2345, some c2351, some c2045, some c2048, some c281, some c321, some c192, some c28, some c2418, some c2419, some c323, some c283, some c268, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2420 : lratChecker f2420 p2420 = .success := by decide +kernel
theorem unsat2420 : Unsatisfiable (PosFin 57) f2420 := by
  apply lratCheckerSound f2420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2420
  · intro a ha; simp [p2420] at ha; subst a; trivial
  · exact checked2420
theorem derived2420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2420 := by
  apply localUnsat_implies_entails f2420 [c2364, c100, c2416, c2230, c2407, c2345, c2351, c2045, c2048, c281, c321, c192, c28, c2418, c2419, c323, c283, c268] c2420 unsat2420 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2416 := derived2416 a h
  have h3 : Entails.eval a c2230 := derived2230 a h
  have h4 : Entails.eval a c2407 := derived2407 a h
  have h5 : Entails.eval a c2345 := derived2345 a h
  have h6 : Entails.eval a c2351 := derived2351 a h
  have h7 : Entails.eval a c2045 := derived2045 a h
  have h8 : Entails.eval a c2048 := derived2048 a h
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c2418 := derived2418 a h
  have h14 : Entails.eval a c2419 := derived2419 a h
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c283 := h 282 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2421 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨44, by decide⟩, true), (⟨55, by decide⟩, true), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c360, some c377, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2421 : lratChecker f2421 p2421 = .success := by decide +kernel
theorem unsat2421 : Unsatisfiable (PosFin 57) f2421 := by
  apply lratCheckerSound f2421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2421
  · intro a ha; simp [p2421] at ha; subst a; trivial
  · exact checked2421
theorem derived2421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2421 := by
  apply localUnsat_implies_entails f2421 [c357, c360, c377] c2421 unsat2421 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2422 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨43, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2407, some c2364, some c100, some c2345, some c2048, some c2045, some c2416, some c2351, some c2391, some c2230, some c2420, some c2421, some c323, some c283, some c195, some c30, some c2418, some c1010, some c374, some c150, some c2049, some c1142, some c2389, some c175, some c137, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2422 : lratChecker f2422 p2422 = .success := by decide +kernel
theorem unsat2422 : Unsatisfiable (PosFin 57) f2422 := by
  apply lratCheckerSound f2422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2422
  · intro a ha; simp [p2422] at ha; subst a; trivial
  · exact checked2422
theorem derived2422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2422 := by
  apply localUnsat_implies_entails f2422 [c2201, c2407, c2364, c100, c2345, c2048, c2045, c2416, c2351, c2391, c2230, c2420, c2421, c323, c283, c195, c30, c2418, c1010, c374, c150, c2049, c1142, c2389, c175, c137] c2422 unsat2422 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2407 := derived2407 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2345 := derived2345 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c2045 := derived2045 a h
  have h7 : Entails.eval a c2416 := derived2416 a h
  have h8 : Entails.eval a c2351 := derived2351 a h
  have h9 : Entails.eval a c2391 := derived2391 a h
  have h10 : Entails.eval a c2230 := derived2230 a h
  have h11 : Entails.eval a c2420 := derived2420 a h
  have h12 : Entails.eval a c2421 := derived2421 a h
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c2418 := derived2418 a h
  have h18 : Entails.eval a c1010 := derived1010 a h
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c2049 := derived2049 a h
  have h22 : Entails.eval a c1142 := derived1142 a h
  have h23 : Entails.eval a c2389 := derived2389 a h
  have h24 : Entails.eval a c175 := h 174 (by decide)
  have h25 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2423 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2416, some c2230, some c2407, some c2345, some c2351, some c2391, some c2417, some c2415, some c2420, some c2422, some c377, some c152, some c2296, some c6, some c160, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2423 : lratChecker f2423 p2423 = .success := by decide +kernel
theorem unsat2423 : Unsatisfiable (PosFin 57) f2423 := by
  apply lratCheckerSound f2423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2423
  · intro a ha; simp [p2423] at ha; subst a; trivial
  · exact checked2423
theorem derived2423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2423 := by
  apply localUnsat_implies_entails f2423 [c2364, c100, c2416, c2230, c2407, c2345, c2351, c2391, c2417, c2415, c2420, c2422, c377, c152, c2296, c6, c160] c2423 unsat2423 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2416 := derived2416 a h
  have h3 : Entails.eval a c2230 := derived2230 a h
  have h4 : Entails.eval a c2407 := derived2407 a h
  have h5 : Entails.eval a c2345 := derived2345 a h
  have h6 : Entails.eval a c2351 := derived2351 a h
  have h7 : Entails.eval a c2391 := derived2391 a h
  have h8 : Entails.eval a c2417 := derived2417 a h
  have h9 : Entails.eval a c2415 := derived2415 a h
  have h10 : Entails.eval a c2420 := derived2420 a h
  have h11 : Entails.eval a c2422 := derived2422 a h
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c2296 := derived2296 a h
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2424 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c100, some c2391, some c2407, some c374, some c2416, some c2230, some c2423, some c2167, some c155, some c2421, some c1051, some c371, some c2415, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2424 : lratChecker f2424 p2424 = .success := by decide +kernel
theorem unsat2424 : Unsatisfiable (PosFin 57) f2424 := by
  apply lratCheckerSound f2424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2424
  · intro a ha; simp [p2424] at ha; subst a; trivial
  · exact checked2424
theorem derived2424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2424 := by
  apply localUnsat_implies_entails f2424 [c2201, c2364, c100, c2391, c2407, c374, c2416, c2230, c2423, c2167, c155, c2421, c1051, c371, c2415] c2424 unsat2424 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2391 := derived2391 a h
  have h4 : Entails.eval a c2407 := derived2407 a h
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c2416 := derived2416 a h
  have h7 : Entails.eval a c2230 := derived2230 a h
  have h8 : Entails.eval a c2423 := derived2423 a h
  have h9 : Entails.eval a c2167 := derived2167 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c2421 := derived2421 a h
  have h12 : Entails.eval a c1051 := derived1051 a h
  have h13 : Entails.eval a c371 := h 370 (by decide)
  have h14 : Entails.eval a c2415 := derived2415 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2425 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2026, some c58, some c59, some c346, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2425 : lratChecker f2425 p2425 = .success := by decide +kernel
theorem unsat2425 : Unsatisfiable (PosFin 57) f2425 := by
  apply lratCheckerSound f2425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2425
  · intro a ha; simp [p2425] at ha; subst a; trivial
  · exact checked2425
theorem derived2425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2425 := by
  apply localUnsat_implies_entails f2425 [c2364, c100, c2345, c2026, c58, c59, c346] c2425 unsat2425 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2026 := derived2026 a h
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2426 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c2424, some c987, some c100, some c2345, some c2425, some c333, some c339, some c2401, some c2047, some c46, some c47, some c306, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2426 : lratChecker f2426 p2426 = .success := by decide +kernel
theorem unsat2426 : Unsatisfiable (PosFin 57) f2426 := by
  apply lratCheckerSound f2426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2426
  · intro a ha; simp [p2426] at ha; subst a; trivial
  · exact checked2426
theorem derived2426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2426 := by
  apply localUnsat_implies_entails f2426 [c2364, c2424, c987, c100, c2345, c2425, c333, c339, c2401, c2047, c46, c47, c306] c2426 unsat2426 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c987 := derived987 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2345 := derived2345 a h
  have h5 : Entails.eval a c2425 := derived2425 a h
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c2401 := derived2401 a h
  have h9 : Entails.eval a c2047 := derived2047 a h
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2427 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨49, by decide⟩, false), (⟨16, by decide⟩, false), (⟨55, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c2424, some c987, some c100, some c2026, some c35, some c1180, some c331, some c299, some c195, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2427 : lratChecker f2427 p2427 = .success := by decide +kernel
theorem unsat2427 : Unsatisfiable (PosFin 57) f2427 := by
  apply lratCheckerSound f2427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2427
  · intro a ha; simp [p2427] at ha; subst a; trivial
  · exact checked2427
theorem derived2427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2427 := by
  apply localUnsat_implies_entails f2427 [c2201, c2364, c2424, c987, c100, c2026, c35, c1180, c331, c299, c195] c2427 unsat2427 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c987 := derived987 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2026 := derived2026 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c1180 := derived1180 a h
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2428 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨42, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2424, some c70, some c2364, some c987, some c100, some c356, some c153, some c376, some c2296, some c841, some c2094, some c1986, some c366, some c2035, some c2426, some c8, some c157, some c2427, some c333, some c339, some c2401, some c2047, some c46, some c306, some c117, some c291, some c864, some c195, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2428 : lratChecker f2428 p2428 = .success := by decide +kernel
theorem unsat2428 : Unsatisfiable (PosFin 57) f2428 := by
  apply lratCheckerSound f2428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2428
  · intro a ha; simp [p2428] at ha; subst a; trivial
  · exact checked2428
theorem derived2428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2428 := by
  apply localUnsat_implies_entails f2428 [c2201, c2345, c2424, c70, c2364, c987, c100, c356, c153, c376, c2296, c841, c2094, c1986, c366, c2035, c2426, c8, c157, c2427, c333, c339, c2401, c2047, c46, c306, c117, c291, c864, c195] c2428 unsat2428 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c2296 := derived2296 a h
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c2094 := derived2094 a h
  have h13 : Entails.eval a c1986 := derived1986 a h
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c2035 := derived2035 a h
  have h16 : Entails.eval a c2426 := derived2426 a h
  have h17 : Entails.eval a c8 := h 7 (by decide)
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c2427 := derived2427 a h
  have h20 : Entails.eval a c333 := h 332 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  have h22 : Entails.eval a c2401 := derived2401 a h
  have h23 : Entails.eval a c2047 := derived2047 a h
  have h24 : Entails.eval a c46 := h 45 (by decide)
  have h25 : Entails.eval a c306 := h 305 (by decide)
  have h26 : Entails.eval a c117 := h 116 (by decide)
  have h27 : Entails.eval a c291 := h 290 (by decide)
  have h28 : Entails.eval a c864 := derived864 a h
  have h29 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2429 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c2424, some c987, some c2345, some c70, some c369, some c100, some c2428, some c2167, some c371, some c2415, some c79, some c2394, some c376, some c1986, some c1051, some c8, some c161, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2429 : lratChecker f2429 p2429 = .success := by decide +kernel
theorem unsat2429 : Unsatisfiable (PosFin 57) f2429 := by
  apply lratCheckerSound f2429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2429
  · intro a ha; simp [p2429] at ha; subst a; trivial
  · exact checked2429
theorem derived2429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2429 := by
  apply localUnsat_implies_entails f2429 [c2201, c2364, c2424, c987, c2345, c70, c369, c100, c2428, c2167, c371, c2415, c79, c2394, c376, c1986, c1051, c8, c161] c2429 unsat2429 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c987 := derived987 a h
  have h4 : Entails.eval a c2345 := derived2345 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c2428 := derived2428 a h
  have h9 : Entails.eval a c2167 := derived2167 a h
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c2415 := derived2415 a h
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c2394 := derived2394 a h
  have h14 : Entails.eval a c376 := h 375 (by decide)
  have h15 : Entails.eval a c1986 := derived1986 a h
  have h16 : Entails.eval a c1051 := derived1051 a h
  have h17 : Entails.eval a c8 := h 7 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2430 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2424, some c70, some c2364, some c100, some c2026, some c58, some c314, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2430 : lratChecker f2430 p2430 = .success := by decide +kernel
theorem unsat2430 : Unsatisfiable (PosFin 57) f2430 := by
  apply lratCheckerSound f2430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2430
  · intro a ha; simp [p2430] at ha; subst a; trivial
  · exact checked2430
theorem derived2430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2430 := by
  apply localUnsat_implies_entails f2430 [c2345, c2424, c70, c2364, c100, c2026, c58, c314] c2430 unsat2430 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c2364 := derived2364 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2026 := derived2026 a h
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2431 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c127, some c265, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p2431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2431 : lratChecker f2431 p2431 = .success := by decide +kernel
theorem unsat2431 : Unsatisfiable (PosFin 57) f2431 := by
  apply lratCheckerSound f2431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2431
  · intro a ha; simp [p2431] at ha; subst a; trivial
  · exact checked2431
theorem derived2431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2431 := by
  apply localUnsat_implies_entails f2431 [c293, c127, c265] c2431 unsat2431 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c127 := h 126 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2432 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2424, some c70, some c2364, some c987, some c100, some c369, some c2428, some c2167, some c371, some c2027, some c2415, some c79, some c2394, some c2429, some c841, some c155, some c16, some c163, some c2430, some c333, some c143, some c2431, some c2047, some c46, some c274, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2432 : lratChecker f2432 p2432 = .success := by decide +kernel
theorem unsat2432 : Unsatisfiable (PosFin 57) f2432 := by
  apply lratCheckerSound f2432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2432
  · intro a ha; simp [p2432] at ha; subst a; trivial
  · exact checked2432
theorem derived2432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2432 := by
  apply localUnsat_implies_entails f2432 [c2201, c2345, c2424, c70, c2364, c987, c100, c369, c2428, c2167, c371, c2027, c2415, c79, c2394, c2429, c841, c155, c16, c163, c2430, c333, c143, c2431, c2047, c46, c274] c2432 unsat2432 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c2428 := derived2428 a h
  have h9 : Entails.eval a c2167 := derived2167 a h
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c2027 := derived2027 a h
  have h12 : Entails.eval a c2415 := derived2415 a h
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c2394 := derived2394 a h
  have h15 : Entails.eval a c2429 := derived2429 a h
  have h16 : Entails.eval a c841 := derived841 a h
  have h17 : Entails.eval a c155 := h 154 (by decide)
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c163 := h 162 (by decide)
  have h20 : Entails.eval a c2430 := derived2430 a h
  have h21 : Entails.eval a c333 := h 332 (by decide)
  have h22 : Entails.eval a c143 := h 142 (by decide)
  have h23 : Entails.eval a c2431 := derived2431 a h
  have h24 : Entails.eval a c2047 := derived2047 a h
  have h25 : Entails.eval a c46 := h 45 (by decide)
  have h26 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2433 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2432, some c2364, some c2424, some c987, some c100, some c153, some c2094, some c12, some c14, some c2296, some c180, some c165, some c376, some c186, some c173, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2433 : lratChecker f2433 p2433 = .success := by decide +kernel
theorem unsat2433 : Unsatisfiable (PosFin 57) f2433 := by
  apply lratCheckerSound f2433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2433
  · intro a ha; simp [p2433] at ha; subst a; trivial
  · exact checked2433
theorem derived2433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2433 := by
  apply localUnsat_implies_entails f2433 [c2201, c2432, c2364, c2424, c987, c100, c153, c2094, c12, c14, c2296, c180, c165, c376, c186, c173] c2433 unsat2433 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2432 := derived2432 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c2424 := derived2424 a h
  have h4 : Entails.eval a c987 := derived987 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c2094 := derived2094 a h
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c2296 := derived2296 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2434 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c6, some c186, some c165, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2434 : lratChecker f2434 p2434 = .success := by decide +kernel
theorem unsat2434 : Unsatisfiable (PosFin 57) f2434 := by
  apply lratCheckerSound f2434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2434
  · intro a ha; simp [p2434] at ha; subst a; trivial
  · exact checked2434
theorem derived2434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2434 := by
  apply localUnsat_implies_entails f2434 [c2364, c6, c186, c165] c2434 unsat2434 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2435 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2432, some c2364, some c2424, some c987, some c100, some c2433, some c2167, some c2260, some c178, some c2434, some c172, some c376, some c361, some c360, some c841, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2435 : lratChecker f2435 p2435 = .success := by decide +kernel
theorem unsat2435 : Unsatisfiable (PosFin 57) f2435 := by
  apply lratCheckerSound f2435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2435
  · intro a ha; simp [p2435] at ha; subst a; trivial
  · exact checked2435
theorem derived2435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2435 := by
  apply localUnsat_implies_entails f2435 [c2432, c2364, c2424, c987, c100, c2433, c2167, c2260, c178, c2434, c172, c376, c361, c360, c841] c2435 unsat2435 (by rfl) a
  have h0 : Entails.eval a c2432 := derived2432 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c987 := derived987 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2433 := derived2433 a h
  have h6 : Entails.eval a c2167 := derived2167 a h
  have h7 : Entails.eval a c2260 := derived2260 a h
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c2434 := derived2434 a h
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c361 := h 360 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2436 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨14, by decide⟩, false), (⟨13, by decide⟩, true), (⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c357, some c186, some c841, some c179, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2436 : lratChecker f2436 p2436 = .success := by decide +kernel
theorem unsat2436 : Unsatisfiable (PosFin 57) f2436 := by
  apply lratCheckerSound f2436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2436
  · intro a ha; simp [p2436] at ha; subst a; trivial
  · exact checked2436
theorem derived2436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2436 := by
  apply localUnsat_implies_entails f2436 [c150, c357, c186, c841, c179] c2436 unsat2436 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2437 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2424, some c70, some c2364, some c987, some c100, some c2432, some c2435, some c370, some c366, some c2428, some c2167, some c2260, some c178, some c2436, some c376, some c360, some c152, some c841, some c1665, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2437 : lratChecker f2437 p2437 = .success := by decide +kernel
theorem unsat2437 : Unsatisfiable (PosFin 57) f2437 := by
  apply lratCheckerSound f2437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2437
  · intro a ha; simp [p2437] at ha; subst a; trivial
  · exact checked2437
theorem derived2437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2437 := by
  apply localUnsat_implies_entails f2437 [c2345, c2424, c70, c2364, c987, c100, c2432, c2435, c370, c366, c2428, c2167, c2260, c178, c2436, c376, c360, c152, c841, c1665] c2437 unsat2437 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c2364 := derived2364 a h
  have h4 : Entails.eval a c987 := derived987 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c2432 := derived2432 a h
  have h7 : Entails.eval a c2435 := derived2435 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c2428 := derived2428 a h
  have h11 : Entails.eval a c2167 := derived2167 a h
  have h12 : Entails.eval a c2260 := derived2260 a h
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c2436 := derived2436 a h
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c841 := derived841 a h
  have h19 : Entails.eval a c1665 := derived1665 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2438 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c277, some c2389, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p2438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2438 : lratChecker f2438 p2438 = .success := by decide +kernel
theorem unsat2438 : Unsatisfiable (PosFin 57) f2438 := by
  apply lratCheckerSound f2438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2438
  · intro a ha; simp [p2438] at ha; subst a; trivial
  · exact checked2438
theorem derived2438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2438 := by
  apply localUnsat_implies_entails f2438 [c317, c277, c2389] c2438 unsat2438 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c2389 := derived2389 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2439 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨56, by decide⟩, false), (⟨47, by decide⟩, false), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2345, some c2424, some c70, some c370, some c2364, some c100, some c173, some c183, some c16, some c169, some c79, some c2425, some c2438, some c2047, some c47, some c292, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2439 : lratChecker f2439 p2439 = .success := by decide +kernel
theorem unsat2439 : Unsatisfiable (PosFin 57) f2439 := by
  apply lratCheckerSound f2439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2439
  · intro a ha; simp [p2439] at ha; subst a; trivial
  · exact checked2439
theorem derived2439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2439 := by
  apply localUnsat_implies_entails f2439 [c2201, c2345, c2424, c70, c370, c2364, c100, c173, c183, c16, c169, c79, c2425, c2438, c2047, c47, c292] c2439 unsat2439 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c2364 := derived2364 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c2425 := derived2425 a h
  have h13 : Entails.eval a c2438 := derived2438 a h
  have h14 : Entails.eval a c2047 := derived2047 a h
  have h15 : Entails.eval a c47 := h 46 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2440 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨42, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2424, some c70, some c2364, some c987, some c100, some c2026, some c35, some c58, some c2430, some c293, some c298, some c319, some c2035, some c264, some c329, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2440 : lratChecker f2440 p2440 = .success := by decide +kernel
theorem unsat2440 : Unsatisfiable (PosFin 57) f2440 := by
  apply lratCheckerSound f2440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2440
  · intro a ha; simp [p2440] at ha; subst a; trivial
  · exact checked2440
theorem derived2440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2440 := by
  apply localUnsat_implies_entails f2440 [c2345, c2424, c70, c2364, c987, c100, c2026, c35, c58, c2430, c293, c298, c319, c2035, c264, c329] c2440 unsat2440 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c2364 := derived2364 a h
  have h4 : Entails.eval a c987 := derived987 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c2026 := derived2026 a h
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c2430 := derived2430 a h
  have h10 : Entails.eval a c293 := h 292 (by decide)
  have h11 : Entails.eval a c298 := h 297 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c2035 := derived2035 a h
  have h14 : Entails.eval a c264 := h 263 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2441 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c298, some c264, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p2441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2441 : lratChecker f2441 p2441 = .success := by decide +kernel
theorem unsat2441 : Unsatisfiable (PosFin 57) f2441 := by
  apply lratCheckerSound f2441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2441
  · intro a ha; simp [p2441] at ha; subst a; trivial
  · exact checked2441
theorem derived2441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2441 := by
  apply localUnsat_implies_entails f2441 [c293, c298, c264] c2441 unsat2441 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2442 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2437, some c2230, some c2424, some c987, some c379, some c2296, some c2345, some c70, some c2151, some c370, some c2365, some c152, some c361, some c2167, some c6, some c167, some c2439, some c2440, some c333, some c338, some c2441, some c2047, some c46, some c274, some c279, some c2035, some c264, some c289, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2442 : lratChecker f2442 p2442 = .success := by decide +kernel
theorem unsat2442 : Unsatisfiable (PosFin 57) f2442 := by
  apply lratCheckerSound f2442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2442
  · intro a ha; simp [p2442] at ha; subst a; trivial
  · exact checked2442
theorem derived2442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2442 := by
  apply localUnsat_implies_entails f2442 [c2364, c100, c2437, c2230, c2424, c987, c379, c2296, c2345, c70, c2151, c370, c2365, c152, c361, c2167, c6, c167, c2439, c2440, c333, c338, c2441, c2047, c46, c274, c279, c2035, c264, c289] c2442 unsat2442 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2437 := derived2437 a h
  have h3 : Entails.eval a c2230 := derived2230 a h
  have h4 : Entails.eval a c2424 := derived2424 a h
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c2296 := derived2296 a h
  have h8 : Entails.eval a c2345 := derived2345 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c2151 := derived2151 a h
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c2365 := derived2365 a h
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c2167 := derived2167 a h
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c167 := h 166 (by decide)
  have h18 : Entails.eval a c2439 := derived2439 a h
  have h19 : Entails.eval a c2440 := derived2440 a h
  have h20 : Entails.eval a c333 := h 332 (by decide)
  have h21 : Entails.eval a c338 := h 337 (by decide)
  have h22 : Entails.eval a c2441 := derived2441 a h
  have h23 : Entails.eval a c2047 := derived2047 a h
  have h24 : Entails.eval a c46 := h 45 (by decide)
  have h25 : Entails.eval a c274 := h 273 (by decide)
  have h26 : Entails.eval a c279 := h 278 (by decide)
  have h27 : Entails.eval a c2035 := derived2035 a h
  have h28 : Entails.eval a c264 := h 263 (by decide)
  have h29 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2443 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2437, some c2345, some c2424, some c70, some c2364, some c987, some c100, some c333, some c321, some c338, some c1655, some c2441, some c192, some c46, some c285, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2443 : lratChecker f2443 p2443 = .success := by decide +kernel
theorem unsat2443 : Unsatisfiable (PosFin 57) f2443 := by
  apply lratCheckerSound f2443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2443
  · intro a ha; simp [p2443] at ha; subst a; trivial
  · exact checked2443
theorem derived2443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2443 := by
  apply localUnsat_implies_entails f2443 [c2437, c2345, c2424, c70, c2364, c987, c100, c333, c321, c338, c1655, c2441, c192, c46, c285] c2443 unsat2443 (by rfl) a
  have h0 : Entails.eval a c2437 := derived2437 a h
  have h1 : Entails.eval a c2345 := derived2345 a h
  have h2 : Entails.eval a c2424 := derived2424 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c338 := h 337 (by decide)
  have h10 : Entails.eval a c1655 := derived1655 a h
  have h11 : Entails.eval a c2441 := derived2441 a h
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2444 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2424, some c70, some c366, some c2035, some c2415, some c2437, some c2364, some c987, some c100, some c2026, some c35, some c58, some c329, some c281, some c298, some c325, some c192, some c193, some c28, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2444 : lratChecker f2444 p2444 = .success := by decide +kernel
theorem unsat2444 : Unsatisfiable (PosFin 57) f2444 := by
  apply lratCheckerSound f2444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2444
  · intro a ha; simp [p2444] at ha; subst a; trivial
  · exact checked2444
theorem derived2444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2444 := by
  apply localUnsat_implies_entails f2444 [c2345, c2424, c70, c366, c2035, c2415, c2437, c2364, c987, c100, c2026, c35, c58, c329, c281, c298, c325, c192, c193, c28] c2444 unsat2444 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2415 := derived2415 a h
  have h6 : Entails.eval a c2437 := derived2437 a h
  have h7 : Entails.eval a c2364 := derived2364 a h
  have h8 : Entails.eval a c987 := derived987 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c2026 := derived2026 a h
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  have h15 : Entails.eval a c298 := h 297 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  have h17 : Entails.eval a c192 := h 191 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  have h19 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2445 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨39, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c281, some c889, some c268, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p2445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2445 : lratChecker f2445 p2445 = .success := by decide +kernel
theorem unsat2445 : Unsatisfiable (PosFin 57) f2445 := by
  apply lratCheckerSound f2445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2445
  · intro a ha; simp [p2445] at ha; subst a; trivial
  · exact checked2445
theorem derived2445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2445 := by
  apply localUnsat_implies_entails f2445 [c281, c889, c268] c2445 unsat2445 (by rfl) a
  have h0 : Entails.eval a c281 := h 280 (by decide)
  have h1 : Entails.eval a c889 := derived889 a h
  have h2 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2446 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2442, some c2364, some c100, some c2437, some c2230, some c2345, some c2424, some c70, some c987, some c2415, some c366, some c2035, some c2444, some c321, some c338, some c2443, some c357, some c323, some c2445, some c2047, some c46, some c289, some c285, some c193, some c192, some c28, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2446 : lratChecker f2446 p2446 = .success := by decide +kernel
theorem unsat2446 : Unsatisfiable (PosFin 57) f2446 := by
  apply lratCheckerSound f2446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2446
  · intro a ha; simp [p2446] at ha; subst a; trivial
  · exact checked2446
theorem derived2446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2446 := by
  apply localUnsat_implies_entails f2446 [c2442, c2364, c100, c2437, c2230, c2345, c2424, c70, c987, c2415, c366, c2035, c2444, c321, c338, c2443, c357, c323, c2445, c2047, c46, c289, c285, c193, c192, c28] c2446 unsat2446 (by rfl) a
  have h0 : Entails.eval a c2442 := derived2442 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2437 := derived2437 a h
  have h4 : Entails.eval a c2230 := derived2230 a h
  have h5 : Entails.eval a c2345 := derived2345 a h
  have h6 : Entails.eval a c2424 := derived2424 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c987 := derived987 a h
  have h9 : Entails.eval a c2415 := derived2415 a h
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c2035 := derived2035 a h
  have h12 : Entails.eval a c2444 := derived2444 a h
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  have h15 : Entails.eval a c2443 := derived2443 a h
  have h16 : Entails.eval a c357 := h 356 (by decide)
  have h17 : Entails.eval a c323 := h 322 (by decide)
  have h18 : Entails.eval a c2445 := derived2445 a h
  have h19 : Entails.eval a c2047 := derived2047 a h
  have h20 : Entails.eval a c46 := h 45 (by decide)
  have h21 : Entails.eval a c289 := h 288 (by decide)
  have h22 : Entails.eval a c285 := h 284 (by decide)
  have h23 : Entails.eval a c193 := h 192 (by decide)
  have h24 : Entails.eval a c192 := h 191 (by decide)
  have h25 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2447 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨15, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2364, some c100, some c2345, some c2026, some c58, some c2425, some c2055, some c16, some c371, some c167, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2447 : lratChecker f2447 p2447 = .success := by decide +kernel
theorem unsat2447 : Unsatisfiable (PosFin 57) f2447 := by
  apply lratCheckerSound f2447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2447
  · intro a ha; simp [p2447] at ha; subst a; trivial
  · exact checked2447
theorem derived2447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2447 := by
  apply localUnsat_implies_entails f2447 [c2201, c2364, c100, c2345, c2026, c58, c2425, c2055, c16, c371, c167] c2447 unsat2447 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2345 := derived2345 a h
  have h4 : Entails.eval a c2026 := derived2026 a h
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c2425 := derived2425 a h
  have h7 : Entails.eval a c2055 := derived2055 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2448 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2446, some c2442, some c2364, some c100, some c2437, some c2230, some c2424, some c987, some c379, some c2296, some c2345, some c70, some c155, some c357, some c2447, some c338, some c2443, some c333, some c2027, some c2441, some c2047, some c46, some c274, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2448 : lratChecker f2448 p2448 = .success := by decide +kernel
theorem unsat2448 : Unsatisfiable (PosFin 57) f2448 := by
  apply lratCheckerSound f2448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2448
  · intro a ha; simp [p2448] at ha; subst a; trivial
  · exact checked2448
theorem derived2448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2448 := by
  apply localUnsat_implies_entails f2448 [c2446, c2442, c2364, c100, c2437, c2230, c2424, c987, c379, c2296, c2345, c70, c155, c357, c2447, c338, c2443, c333, c2027, c2441, c2047, c46, c274] c2448 unsat2448 (by rfl) a
  have h0 : Entails.eval a c2446 := derived2446 a h
  have h1 : Entails.eval a c2442 := derived2442 a h
  have h2 : Entails.eval a c2364 := derived2364 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2437 := derived2437 a h
  have h5 : Entails.eval a c2230 := derived2230 a h
  have h6 : Entails.eval a c2424 := derived2424 a h
  have h7 : Entails.eval a c987 := derived987 a h
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c2296 := derived2296 a h
  have h10 : Entails.eval a c2345 := derived2345 a h
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c2447 := derived2447 a h
  have h15 : Entails.eval a c338 := h 337 (by decide)
  have h16 : Entails.eval a c2443 := derived2443 a h
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c2027 := derived2027 a h
  have h19 : Entails.eval a c2441 := derived2441 a h
  have h20 : Entails.eval a c2047 := derived2047 a h
  have h21 : Entails.eval a c46 := h 45 (by decide)
  have h22 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2449 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2442, some c2364, some c100, some c2437, some c2230, some c2424, some c987, some c379, some c2296, some c2345, some c2446, some c2448, some c2167, some c160, some c167, some c8, some c79, some c2425, some c321, some c2443, some c323, some c2445, some c2047, some c46, some c47, some c306, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2449 : lratChecker f2449 p2449 = .success := by decide +kernel
theorem unsat2449 : Unsatisfiable (PosFin 57) f2449 := by
  apply lratCheckerSound f2449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2449
  · intro a ha; simp [p2449] at ha; subst a; trivial
  · exact checked2449
theorem derived2449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2449 := by
  apply localUnsat_implies_entails f2449 [c2442, c2364, c100, c2437, c2230, c2424, c987, c379, c2296, c2345, c2446, c2448, c2167, c160, c167, c8, c79, c2425, c321, c2443, c323, c2445, c2047, c46, c47, c306] c2449 unsat2449 (by rfl) a
  have h0 : Entails.eval a c2442 := derived2442 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2437 := derived2437 a h
  have h4 : Entails.eval a c2230 := derived2230 a h
  have h5 : Entails.eval a c2424 := derived2424 a h
  have h6 : Entails.eval a c987 := derived987 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c2296 := derived2296 a h
  have h9 : Entails.eval a c2345 := derived2345 a h
  have h10 : Entails.eval a c2446 := derived2446 a h
  have h11 : Entails.eval a c2448 := derived2448 a h
  have h12 : Entails.eval a c2167 := derived2167 a h
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c79 := h 78 (by decide)
  have h17 : Entails.eval a c2425 := derived2425 a h
  have h18 : Entails.eval a c321 := h 320 (by decide)
  have h19 : Entails.eval a c2443 := derived2443 a h
  have h20 : Entails.eval a c323 := h 322 (by decide)
  have h21 : Entails.eval a c2445 := derived2445 a h
  have h22 : Entails.eval a c2047 := derived2047 a h
  have h23 : Entails.eval a c46 := h 45 (by decide)
  have h24 : Entails.eval a c47 := h 46 (by decide)
  have h25 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2450 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c2424, some c987, some c100, some c2437, some c2230, some c379, some c2296, some c2442, some c2449, some c2365, some c152, some c2167, some c6, some c160, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2450 : lratChecker f2450 p2450 = .success := by decide +kernel
theorem unsat2450 : Unsatisfiable (PosFin 57) f2450 := by
  apply lratCheckerSound f2450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2450
  · intro a ha; simp [p2450] at ha; subst a; trivial
  · exact checked2450
theorem derived2450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2450 := by
  apply localUnsat_implies_entails f2450 [c2364, c2424, c987, c100, c2437, c2230, c379, c2296, c2442, c2449, c2365, c152, c2167, c6, c160] c2450 unsat2450 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c987 := derived987 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2437 := derived2437 a h
  have h5 : Entails.eval a c2230 := derived2230 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c2296 := derived2296 a h
  have h8 : Entails.eval a c2442 := derived2442 a h
  have h9 : Entails.eval a c2449 := derived2449 a h
  have h10 : Entails.eval a c2365 := derived2365 a h
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c2167 := derived2167 a h
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2451 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2424, some c2450, some c94, some c2364, some c987, some c100, some c58, some c62, some c338, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2451 : lratChecker f2451 p2451 = .success := by decide +kernel
theorem unsat2451 : Unsatisfiable (PosFin 57) f2451 := by
  apply lratCheckerSound f2451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2451
  · intro a ha; simp [p2451] at ha; subst a; trivial
  · exact checked2451
theorem derived2451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2451 := by
  apply localUnsat_implies_entails f2451 [c2345, c2424, c2450, c94, c2364, c987, c100, c58, c62, c338] c2451 unsat2451 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c2450 := derived2450 a h
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c2364 := derived2364 a h
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2452 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨45, by decide⟩, true), (⟨19, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c1051, some c16, some c167, some c188, some c181, some c111, some c106, some c240, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2452 : lratChecker f2452 p2452 = .success := by decide +kernel
theorem unsat2452 : Unsatisfiable (PosFin 57) f2452 := by
  apply lratCheckerSound f2452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2452
  · intro a ha; simp [p2452] at ha; subst a; trivial
  · exact checked2452
theorem derived2452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2452 := by
  apply localUnsat_implies_entails f2452 [c2201, c1051, c16, c167, c188, c181, c111, c106, c240] c2452 unsat2452 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c1051 := derived1051 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2453 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c100, some c2345, some c2424, some c70, some c987, some c2450, some c94, some c1543, some c2451, some c2062, some c2027, some c2035, some c379, some c596, some c369, some c285, some c1654, some c325, some c192, some c229, some c371, some c83, some c2452, some c176, some c180, some c6, some c160, some c157, some c2020, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2453 : lratChecker f2453 p2453 = .success := by decide +kernel
theorem unsat2453 : Unsatisfiable (PosFin 57) f2453 := by
  apply lratCheckerSound f2453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2453
  · intro a ha; simp [p2453] at ha; subst a; trivial
  · exact checked2453
theorem derived2453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2453 := by
  apply localUnsat_implies_entails f2453 [c2364, c100, c2345, c2424, c70, c987, c2450, c94, c1543, c2451, c2062, c2027, c2035, c379, c596, c369, c285, c1654, c325, c192, c229, c371, c83, c2452, c176, c180, c6, c160, c157, c2020] c2453 unsat2453 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c2345 := derived2345 a h
  have h3 : Entails.eval a c2424 := derived2424 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c2450 := derived2450 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c1543 := derived1543 a h
  have h9 : Entails.eval a c2451 := derived2451 a h
  have h10 : Entails.eval a c2062 := derived2062 a h
  have h11 : Entails.eval a c2027 := derived2027 a h
  have h12 : Entails.eval a c2035 := derived2035 a h
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c596 := derived596 a h
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c285 := h 284 (by decide)
  have h17 : Entails.eval a c1654 := derived1654 a h
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c229 := h 228 (by decide)
  have h21 : Entails.eval a c371 := h 370 (by decide)
  have h22 : Entails.eval a c83 := h 82 (by decide)
  have h23 : Entails.eval a c2452 := derived2452 a h
  have h24 : Entails.eval a c176 := h 175 (by decide)
  have h25 : Entails.eval a c180 := h 179 (by decide)
  have h26 : Entails.eval a c6 := h 5 (by decide)
  have h27 : Entails.eval a c160 := h 159 (by decide)
  have h28 : Entails.eval a c157 := h 156 (by decide)
  have h29 : Entails.eval a c2020 := derived2020 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2454 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2364, some c2424, some c987, some c2345, some c2450, some c94, some c379, some c2453, some c152, some c6, some c100, some c2365, some c2167, some c70, some c1543, some c2451, some c2062, some c596, some c160, some c157, some c2020, some c181, some c180, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2454 : lratChecker f2454 p2454 = .success := by decide +kernel
theorem unsat2454 : Unsatisfiable (PosFin 57) f2454 := by
  apply lratCheckerSound f2454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2454
  · intro a ha; simp [p2454] at ha; subst a; trivial
  · exact checked2454
theorem derived2454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2454 := by
  apply localUnsat_implies_entails f2454 [c2364, c2424, c987, c2345, c2450, c94, c379, c2453, c152, c6, c100, c2365, c2167, c70, c1543, c2451, c2062, c596, c160, c157, c2020, c181, c180] c2454 unsat2454 (by rfl) a
  have h0 : Entails.eval a c2364 := derived2364 a h
  have h1 : Entails.eval a c2424 := derived2424 a h
  have h2 : Entails.eval a c987 := derived987 a h
  have h3 : Entails.eval a c2345 := derived2345 a h
  have h4 : Entails.eval a c2450 := derived2450 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c2453 := derived2453 a h
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c2365 := derived2365 a h
  have h12 : Entails.eval a c2167 := derived2167 a h
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c1543 := derived1543 a h
  have h15 : Entails.eval a c2451 := derived2451 a h
  have h16 : Entails.eval a c2062 := derived2062 a h
  have h17 : Entails.eval a c596 := derived596 a h
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c157 := h 156 (by decide)
  have h20 : Entails.eval a c2020 := derived2020 a h
  have h21 : Entails.eval a c181 := h 180 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2455 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2345, some c2364, some c100, some c2424, some c987, some c70, some c2450, some c596, some c94, some c1543, some c379, some c2451, some c2062, some c2035, some c2027, some c2453, some c2365, some c152, some c2167, some c2454, some c370, some c279, some c319, some c83, some c190, some c22, some c225, some c2452, some c180, some c129, some c145, some c192, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked2455 : lratChecker f2455 p2455 = .success := by decide +kernel
theorem unsat2455 : Unsatisfiable (PosFin 57) f2455 := by
  apply lratCheckerSound f2455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2455
  · intro a ha; simp [p2455] at ha; subst a; trivial
  · exact checked2455
theorem derived2455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2455 := by
  apply localUnsat_implies_entails f2455 [c2345, c2364, c100, c2424, c987, c70, c2450, c596, c94, c1543, c379, c2451, c2062, c2035, c2027, c2453, c2365, c152, c2167, c2454, c370, c279, c319, c83, c190, c22, c225, c2452, c180, c129, c145, c192] c2455 unsat2455 (by rfl) a
  have h0 : Entails.eval a c2345 := derived2345 a h
  have h1 : Entails.eval a c2364 := derived2364 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2424 := derived2424 a h
  have h4 : Entails.eval a c987 := derived987 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c2450 := derived2450 a h
  have h7 : Entails.eval a c596 := derived596 a h
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c1543 := derived1543 a h
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c2451 := derived2451 a h
  have h12 : Entails.eval a c2062 := derived2062 a h
  have h13 : Entails.eval a c2035 := derived2035 a h
  have h14 : Entails.eval a c2027 := derived2027 a h
  have h15 : Entails.eval a c2453 := derived2453 a h
  have h16 : Entails.eval a c2365 := derived2365 a h
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c2167 := derived2167 a h
  have h19 : Entails.eval a c2454 := derived2454 a h
  have h20 : Entails.eval a c370 := h 369 (by decide)
  have h21 : Entails.eval a c279 := h 278 (by decide)
  have h22 : Entails.eval a c319 := h 318 (by decide)
  have h23 : Entails.eval a c83 := h 82 (by decide)
  have h24 : Entails.eval a c190 := h 189 (by decide)
  have h25 : Entails.eval a c22 := h 21 (by decide)
  have h26 : Entails.eval a c225 := h 224 (by decide)
  have h27 : Entails.eval a c2452 := derived2452 a h
  have h28 : Entails.eval a c180 := h 179 (by decide)
  have h29 : Entails.eval a c129 := h 128 (by decide)
  have h30 : Entails.eval a c145 := h 144 (by decide)
  have h31 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2456 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2037, some c2268, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2456 : lratChecker f2456 p2456 = .success := by decide +kernel
theorem unsat2456 : Unsatisfiable (PosFin 57) f2456 := by
  apply lratCheckerSound f2456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2456
  · intro a ha; simp [p2456] at ha; subst a; trivial
  · exact checked2456
theorem derived2456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2456 := by
  apply localUnsat_implies_entails f2456 [c2455, c2037, c2268] c2456 unsat2456 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c2268 := derived2268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2457 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2064, some c2456, some c2323, some c2050, some c2026, some c2033, some c348, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2457 : lratChecker f2457 p2457 = .success := by decide +kernel
theorem unsat2457 : Unsatisfiable (PosFin 57) f2457 := by
  apply lratCheckerSound f2457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2457
  · intro a ha; simp [p2457] at ha; subst a; trivial
  · exact checked2457
theorem derived2457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2457 := by
  apply localUnsat_implies_entails f2457 [c2455, c2064, c2456, c2323, c2050, c2026, c2033, c348] c2457 unsat2457 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2064 := derived2064 a h
  have h2 : Entails.eval a c2456 := derived2456 a h
  have h3 : Entails.eval a c2323 := derived2323 a h
  have h4 : Entails.eval a c2050 := derived2050 a h
  have h5 : Entails.eval a c2026 := derived2026 a h
  have h6 : Entails.eval a c2033 := derived2033 a h
  have h7 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2458 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2027, some c67, some c93, some c2399, some c337, some c61, some c2033, some c316, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2458 : lratChecker f2458 p2458 = .success := by decide +kernel
theorem unsat2458 : Unsatisfiable (PosFin 57) f2458 := by
  apply lratCheckerSound f2458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2458
  · intro a ha; simp [p2458] at ha; subst a; trivial
  · exact checked2458
theorem derived2458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2458 := by
  apply localUnsat_implies_entails f2458 [c2455, c2027, c67, c93, c2399, c337, c61, c2033, c316] c2458 unsat2458 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2027 := derived2027 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c2399 := derived2399 a h
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c2033 := derived2033 a h
  have h8 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2459 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨53, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c104, some c368, some c2027, some c67, some c370, some c2151, some c841, some c2458, some c102, some c2064, some c1982, some c2456, some c2457, some c291, some c362, some c273, some c864, some c195, some c331, some c339, some c2026, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2459 : lratChecker f2459 p2459 = .success := by decide +kernel
theorem unsat2459 : Unsatisfiable (PosFin 57) f2459 := by
  apply lratCheckerSound f2459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2459
  · intro a ha; simp [p2459] at ha; subst a; trivial
  · exact checked2459
theorem derived2459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2459 := by
  apply localUnsat_implies_entails f2459 [c2455, c2201, c104, c368, c2027, c67, c370, c2151, c841, c2458, c102, c2064, c1982, c2456, c2457, c291, c362, c273, c864, c195, c331, c339, c2026] c2459 unsat2459 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c2027 := derived2027 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c2151 := derived2151 a h
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c2458 := derived2458 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c2064 := derived2064 a h
  have h12 : Entails.eval a c1982 := derived1982 a h
  have h13 : Entails.eval a c2456 := derived2456 a h
  have h14 : Entails.eval a c2457 := derived2457 a h
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c362 := h 361 (by decide)
  have h17 : Entails.eval a c273 := h 272 (by decide)
  have h18 : Entails.eval a c864 := derived864 a h
  have h19 : Entails.eval a c195 := h 194 (by decide)
  have h20 : Entails.eval a c331 := h 330 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  have h22 : Entails.eval a c2026 := derived2026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2460 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2027, some c367, some c67, some c2399, some c2458, some c1039, some c2023, some c2037, some c316, some c337, some c61, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2460 : lratChecker f2460 p2460 = .success := by decide +kernel
theorem unsat2460 : Unsatisfiable (PosFin 57) f2460 := by
  apply lratCheckerSound f2460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2460
  · intro a ha; simp [p2460] at ha; subst a; trivial
  · exact checked2460
theorem derived2460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2460 := by
  apply localUnsat_implies_entails f2460 [c2455, c2027, c367, c67, c2399, c2458, c1039, c2023, c2037, c316, c337, c61] c2460 unsat2460 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2027 := derived2027 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c2399 := derived2399 a h
  have h5 : Entails.eval a c2458 := derived2458 a h
  have h6 : Entails.eval a c1039 := derived1039 a h
  have h7 : Entails.eval a c2023 := derived2023 a h
  have h8 : Entails.eval a c2037 := derived2037 a h
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c337 := h 336 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2461 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c368, some c2027, some c367, some c370, some c2151, some c2460, some c102, some c2456, some c1039, some c2261, some c2459, some c179, some c155, some c14, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2461 : lratChecker f2461 p2461 = .success := by decide +kernel
theorem unsat2461 : Unsatisfiable (PosFin 57) f2461 := by
  apply lratCheckerSound f2461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2461
  · intro a ha; simp [p2461] at ha; subst a; trivial
  · exact checked2461
theorem derived2461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2461 := by
  apply localUnsat_implies_entails f2461 [c2201, c104, c368, c2027, c367, c370, c2151, c2460, c102, c2456, c1039, c2261, c2459, c179, c155, c14] c2461 unsat2461 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c2027 := derived2027 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c2151 := derived2151 a h
  have h7 : Entails.eval a c2460 := derived2460 a h
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c2456 := derived2456 a h
  have h10 : Entails.eval a c1039 := derived1039 a h
  have h11 : Entails.eval a c2261 := derived2261 a h
  have h12 : Entails.eval a c2459 := derived2459 a h
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2462 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨32, by decide⟩, true), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c329, some c271, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p2462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2462 : lratChecker f2462 p2462 = .success := by decide +kernel
theorem unsat2462 : Unsatisfiable (PosFin 57) f2462 := by
  apply lratCheckerSound f2462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2462
  · intro a ha; simp [p2462] at ha; subst a; trivial
  · exact checked2462
theorem derived2462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2462 := by
  apply localUnsat_implies_entails f2462 [c316, c329, c271] c2462 unsat2462 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c329 := h 328 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2463 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c104, some c2151, some c370, some c368, some c2027, some c2460, some c102, some c2064, some c1982, some c2456, some c2461, some c289, some c2462, some c2050, some c2026, some c2033, some c348, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2463 : lratChecker f2463 p2463 = .success := by decide +kernel
theorem unsat2463 : Unsatisfiable (PosFin 57) f2463 := by
  apply lratCheckerSound f2463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2463
  · intro a ha; simp [p2463] at ha; subst a; trivial
  · exact checked2463
theorem derived2463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2463 := by
  apply localUnsat_implies_entails f2463 [c2201, c2455, c104, c2151, c370, c368, c2027, c2460, c102, c2064, c1982, c2456, c2461, c289, c2462, c2050, c2026, c2033, c348] c2463 unsat2463 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c2460 := derived2460 a h
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c2064 := derived2064 a h
  have h10 : Entails.eval a c1982 := derived1982 a h
  have h11 : Entails.eval a c2456 := derived2456 a h
  have h12 : Entails.eval a c2461 := derived2461 a h
  have h13 : Entails.eval a c289 := h 288 (by decide)
  have h14 : Entails.eval a c2462 := derived2462 a h
  have h15 : Entails.eval a c2050 := derived2050 a h
  have h16 : Entails.eval a c2026 := derived2026 a h
  have h17 : Entails.eval a c2033 := derived2033 a h
  have h18 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2464 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2463, some c104, some c2093, some c2349, some c2456, some c66, some c367, some c1039, some c2255, some c2205, some c977, some c179, some c177, some c14, some c161, some c168, some c185, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2464 : lratChecker f2464 p2464 = .success := by decide +kernel
theorem unsat2464 : Unsatisfiable (PosFin 57) f2464 := by
  apply lratCheckerSound f2464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2464
  · intro a ha; simp [p2464] at ha; subst a; trivial
  · exact checked2464
theorem derived2464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2464 := by
  apply localUnsat_implies_entails f2464 [c2201, c2463, c104, c2093, c2349, c2456, c66, c367, c1039, c2255, c2205, c977, c179, c177, c14, c161, c168, c185] c2464 unsat2464 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2463 := derived2463 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2093 := derived2093 a h
  have h4 : Entails.eval a c2349 := derived2349 a h
  have h5 : Entails.eval a c2456 := derived2456 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c1039 := derived1039 a h
  have h9 : Entails.eval a c2255 := derived2255 a h
  have h10 : Entails.eval a c2205 := derived2205 a h
  have h11 : Entails.eval a c977 := derived977 a h
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c161 := h 160 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2465 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c91, some c2458, some c93, some c1287, some c376, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2465 : lratChecker f2465 p2465 = .success := by decide +kernel
theorem unsat2465 : Unsatisfiable (PosFin 57) f2465 := by
  apply lratCheckerSound f2465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2465
  · intro a ha; simp [p2465] at ha; subst a; trivial
  · exact checked2465
theorem derived2465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2465 := by
  apply localUnsat_implies_entails f2465 [c2455, c91, c2458, c93, c1287, c376] c2465 unsat2465 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c2458 := derived2458 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2466 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2037, some c2036, some c376, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2466 : lratChecker f2466 p2466 = .success := by decide +kernel
theorem unsat2466 : Unsatisfiable (PosFin 57) f2466 := by
  apply lratCheckerSound f2466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2466
  · intro a ha; simp [p2466] at ha; subst a; trivial
  · exact checked2466
theorem derived2466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2466 := by
  apply localUnsat_implies_entails f2466 [c2455, c2037, c2036, c376] c2466 unsat2466 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c2036 := derived2036 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2467 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c70, some c78, some c1287, some c2466, some c2048, some c2045, some c281, some c321, some c36, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2467 : lratChecker f2467 p2467 = .success := by decide +kernel
theorem unsat2467 : Unsatisfiable (PosFin 57) f2467 := by
  apply lratCheckerSound f2467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2467
  · intro a ha; simp [p2467] at ha; subst a; trivial
  · exact checked2467
theorem derived2467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2467 := by
  apply localUnsat_implies_entails f2467 [c2455, c70, c78, c1287, c2466, c2048, c2045, c281, c321, c36] c2467 unsat2467 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c2466 := derived2466 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c2045 := derived2045 a h
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2468 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c35, some c58, some c281, some c325, some c36, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2468 : lratChecker f2468 p2468 = .success := by decide +kernel
theorem unsat2468 : Unsatisfiable (PosFin 57) f2468 := by
  apply lratCheckerSound f2468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2468
  · intro a ha; simp [p2468] at ha; subst a; trivial
  · exact checked2468
theorem derived2468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2468 := by
  apply localUnsat_implies_entails f2468 [c2455, c35, c58, c281, c325, c36] c2468 unsat2468 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2469 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2468, some c321, some c36, some c285, some c281, some c46, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2469 : lratChecker f2469 p2469 = .success := by decide +kernel
theorem unsat2469 : Unsatisfiable (PosFin 57) f2469 := by
  apply lratCheckerSound f2469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2469
  · intro a ha; simp [p2469] at ha; subst a; trivial
  · exact checked2469
theorem derived2469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2469 := by
  apply localUnsat_implies_entails f2469 [c2455, c2468, c321, c36, c285, c281, c46] c2469 unsat2469 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2468 := derived2468 a h
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c281 := h 280 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2470 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2467, some c366, some c2027, some c2469, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2470 : lratChecker f2470 p2470 = .success := by decide +kernel
theorem unsat2470 : Unsatisfiable (PosFin 57) f2470 := by
  apply lratCheckerSound f2470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2470
  · intro a ha; simp [p2470] at ha; subst a; trivial
  · exact checked2470
theorem derived2470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2470 := by
  apply localUnsat_implies_entails f2470 [c2467, c366, c2027, c2469] c2470 unsat2470 (by rfl) a
  have h0 : Entails.eval a c2467 := derived2467 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c2027 := derived2027 a h
  have h3 : Entails.eval a c2469 := derived2469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2471 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2465, some c2460, some c371, some c1287, some c362, some c378, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2471 : lratChecker f2471 p2471 = .success := by decide +kernel
theorem unsat2471 : Unsatisfiable (PosFin 57) f2471 := by
  apply lratCheckerSound f2471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2471
  · intro a ha; simp [p2471] at ha; subst a; trivial
  · exact checked2471
theorem derived2471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2471 := by
  apply localUnsat_implies_entails f2471 [c2465, c2460, c371, c1287, c362, c378] c2471 unsat2471 (by rfl) a
  have h0 : Entails.eval a c2465 := derived2465 a h
  have h1 : Entails.eval a c2460 := derived2460 a h
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2472 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2465, some c2471, some c366, some c2035, some c2027, some c1128, some c292, some c2059, some c2047, some c281, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2472 : lratChecker f2472 p2472 = .success := by decide +kernel
theorem unsat2472 : Unsatisfiable (PosFin 57) f2472 := by
  apply lratCheckerSound f2472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2472
  · intro a ha; simp [p2472] at ha; subst a; trivial
  · exact checked2472
theorem derived2472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2472 := by
  apply localUnsat_implies_entails f2472 [c2455, c2465, c2471, c366, c2035, c2027, c1128, c292, c2059, c2047, c281] c2472 unsat2472 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2465 := derived2465 a h
  have h2 : Entails.eval a c2471 := derived2471 a h
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2027 := derived2027 a h
  have h6 : Entails.eval a c1128 := derived1128 a h
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c2059 := derived2059 a h
  have h9 : Entails.eval a c2047 := derived2047 a h
  have h10 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2473 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c2464, some c2470, some c102, some c2472, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2473 : lratChecker f2473 p2473 = .success := by decide +kernel
theorem unsat2473 : Unsatisfiable (PosFin 57) f2473 := by
  apply lratCheckerSound f2473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2473
  · intro a ha; simp [p2473] at ha; subst a; trivial
  · exact checked2473
theorem derived2473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2473 := by
  apply localUnsat_implies_entails f2473 [c2201, c104, c2464, c2470, c102, c2472] c2473 unsat2473 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c2464 := derived2464 a h
  have h3 : Entails.eval a c2470 := derived2470 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c2472 := derived2472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2474 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c329, some c2462, some c270, some c2067, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p2474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2474 : lratChecker f2474 p2474 = .success := by decide +kernel
theorem unsat2474 : Unsatisfiable (PosFin 57) f2474 := by
  apply lratCheckerSound f2474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2474
  · intro a ha; simp [p2474] at ha; subst a; trivial
  · exact checked2474
theorem derived2474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2474 := by
  apply localUnsat_implies_entails f2474 [c329, c2462, c270, c2067] c2474 unsat2474 (by rfl) a
  have h0 : Entails.eval a c329 := h 328 (by decide)
  have h1 : Entails.eval a c2462 := derived2462 a h
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2475 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2349, some c2230, some c367, some c364, some c2456, some c2097, some c330, some c2474, some c298, some c289, some c2047, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2475 : lratChecker f2475 p2475 = .success := by decide +kernel
theorem unsat2475 : Unsatisfiable (PosFin 57) f2475 := by
  apply lratCheckerSound f2475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2475
  · intro a ha; simp [p2475] at ha; subst a; trivial
  · exact checked2475
theorem derived2475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2475 := by
  apply localUnsat_implies_entails f2475 [c2349, c2230, c367, c364, c2456, c2097, c330, c2474, c298, c289, c2047] c2475 unsat2475 (by rfl) a
  have h0 : Entails.eval a c2349 := derived2349 a h
  have h1 : Entails.eval a c2230 := derived2230 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c364 := h 363 (by decide)
  have h4 : Entails.eval a c2456 := derived2456 a h
  have h5 : Entails.eval a c2097 := derived2097 a h
  have h6 : Entails.eval a c330 := h 329 (by decide)
  have h7 : Entails.eval a c2474 := derived2474 a h
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c289 := h 288 (by decide)
  have h10 : Entails.eval a c2047 := derived2047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2476 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c104, some c2473, some c2230, some c2463, some c2093, some c2349, some c2456, some c66, some c367, some c2255, some c155, some c364, some c1039, some c14, some c1248, some c977, some c177, some c2475, some c67, some c1118, some c1245, some c184, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2476 : lratChecker f2476 p2476 = .success := by decide +kernel
theorem unsat2476 : Unsatisfiable (PosFin 57) f2476 := by
  apply lratCheckerSound f2476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2476
  · intro a ha; simp [p2476] at ha; subst a; trivial
  · exact checked2476
theorem derived2476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2476 := by
  apply localUnsat_implies_entails f2476 [c2201, c2455, c104, c2473, c2230, c2463, c2093, c2349, c2456, c66, c367, c2255, c155, c364, c1039, c14, c1248, c977, c177, c2475, c67, c1118, c1245, c184] c2476 unsat2476 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2473 := derived2473 a h
  have h4 : Entails.eval a c2230 := derived2230 a h
  have h5 : Entails.eval a c2463 := derived2463 a h
  have h6 : Entails.eval a c2093 := derived2093 a h
  have h7 : Entails.eval a c2349 := derived2349 a h
  have h8 : Entails.eval a c2456 := derived2456 a h
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c2255 := derived2255 a h
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c364 := h 363 (by decide)
  have h14 : Entails.eval a c1039 := derived1039 a h
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c1248 := derived1248 a h
  have h17 : Entails.eval a c977 := derived977 a h
  have h18 : Entails.eval a c177 := h 176 (by decide)
  have h19 : Entails.eval a c2475 := derived2475 a h
  have h20 : Entails.eval a c67 := h 66 (by decide)
  have h21 : Entails.eval a c1118 := derived1118 a h
  have h22 : Entails.eval a c1245 := derived1245 a h
  have h23 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2477 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2027, some c366, some c78, some c2460, some c102, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2477 : lratChecker f2477 p2477 = .success := by decide +kernel
theorem unsat2477 : Unsatisfiable (PosFin 57) f2477 := by
  apply lratCheckerSound f2477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2477
  · intro a ha; simp [p2477] at ha; subst a; trivial
  · exact checked2477
theorem derived2477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2477 := by
  apply localUnsat_implies_entails f2477 [c2027, c366, c78, c2460, c102] c2477 unsat2477 (by rfl) a
  have h0 : Entails.eval a c2027 := derived2027 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c2460 := derived2460 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2478 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c91, some c93, some c379, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2478 : lratChecker f2478 p2478 = .success := by decide +kernel
theorem unsat2478 : Unsatisfiable (PosFin 57) f2478 := by
  apply lratCheckerSound f2478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2478
  · intro a ha; simp [p2478] at ha; subst a; trivial
  · exact checked2478
theorem derived2478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2478 := by
  apply localUnsat_implies_entails f2478 [c2455, c91, c93, c379] c2478 unsat2478 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2479 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2059, some c2047, some c281, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2479 : lratChecker f2479 p2479 = .success := by decide +kernel
theorem unsat2479 : Unsatisfiable (PosFin 57) f2479 := by
  apply lratCheckerSound f2479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2479
  · intro a ha; simp [p2479] at ha; subst a; trivial
  · exact checked2479
theorem derived2479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2479 := by
  apply localUnsat_implies_entails f2479 [c2455, c2059, c2047, c281] c2479 unsat2479 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2059 := derived2059 a h
  have h2 : Entails.eval a c2047 := derived2047 a h
  have h3 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2480 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2479, some c1128, some c2478, some c276, some c292, some c2035, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2480 : lratChecker f2480 p2480 = .success := by decide +kernel
theorem unsat2480 : Unsatisfiable (PosFin 57) f2480 := by
  apply lratCheckerSound f2480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2480
  · intro a ha; simp [p2480] at ha; subst a; trivial
  · exact checked2480
theorem derived2480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2480 := by
  apply localUnsat_implies_entails f2480 [c2455, c2479, c1128, c2478, c276, c292, c2035] c2480 unsat2480 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2479 := derived2479 a h
  have h2 : Entails.eval a c1128 := derived1128 a h
  have h3 : Entails.eval a c2478 := derived2478 a h
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c2035 := derived2035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2480

end CochromaticTwenty.Certificates.B16_8_2
