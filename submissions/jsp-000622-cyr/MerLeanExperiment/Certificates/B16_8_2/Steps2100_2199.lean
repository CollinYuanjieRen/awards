import MerLeanExperiment.Certificates.B16_8_2.Steps2000_2099

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2481 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c2473, some c2476, some c2477, some c2480, some c371, some c2230, some c2463, some c357, some c2255, some c155, some c980, some c14, some c16, some c1245, some c166, some c177, some c185, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2481 : lratChecker f2481 p2481 = .success := by decide +kernel
theorem unsat2481 : Unsatisfiable (PosFin 57) f2481 := by
  apply lratCheckerSound f2481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2481
  · intro a ha; simp [p2481] at ha; subst a; trivial
  · exact checked2481
theorem derived2481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2481 := by
  apply localUnsat_implies_entails f2481 [c2201, c104, c2473, c2476, c2477, c2480, c371, c2230, c2463, c357, c2255, c155, c980, c14, c16, c1245, c166, c177, c185] c2481 unsat2481 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c2473 := derived2473 a h
  have h3 : Entails.eval a c2476 := derived2476 a h
  have h4 : Entails.eval a c2477 := derived2477 a h
  have h5 : Entails.eval a c2480 := derived2480 a h
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c2230 := derived2230 a h
  have h8 : Entails.eval a c2463 := derived2463 a h
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c2255 := derived2255 a h
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c980 := derived980 a h
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c1245 := derived1245 a h
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c177 := h 176 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2482 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2476, some c104, some c2473, some c2477, some c2480, some c102, some c70, some c2481, some c367, some c2035, some c2048, some c2045, some c281, some c321, some c36, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2482 : lratChecker f2482 p2482 = .success := by decide +kernel
theorem unsat2482 : Unsatisfiable (PosFin 57) f2482 := by
  apply lratCheckerSound f2482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2482
  · intro a ha; simp [p2482] at ha; subst a; trivial
  · exact checked2482
theorem derived2482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2482 := by
  apply localUnsat_implies_entails f2482 [c2201, c2455, c2476, c104, c2473, c2477, c2480, c102, c70, c2481, c367, c2035, c2048, c2045, c281, c321, c36] c2482 unsat2482 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2476 := derived2476 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2473 := derived2473 a h
  have h5 : Entails.eval a c2477 := derived2477 a h
  have h6 : Entails.eval a c2480 := derived2480 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c2481 := derived2481 a h
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c2035 := derived2035 a h
  have h12 : Entails.eval a c2048 := derived2048 a h
  have h13 : Entails.eval a c2045 := derived2045 a h
  have h14 : Entails.eval a c281 := h 280 (by decide)
  have h15 : Entails.eval a c321 := h 320 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2483 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c2473, some c2476, some c2477, some c2480, some c102, some c2482, some c2469, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2483 : lratChecker f2483 p2483 = .success := by decide +kernel
theorem unsat2483 : Unsatisfiable (PosFin 57) f2483 := by
  apply lratCheckerSound f2483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2483
  · intro a ha; simp [p2483] at ha; subst a; trivial
  · exact checked2483
theorem derived2483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2483 := by
  apply localUnsat_implies_entails f2483 [c2201, c104, c2473, c2476, c2477, c2480, c102, c2482, c2469] c2483 unsat2483 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c2473 := derived2473 a h
  have h3 : Entails.eval a c2476 := derived2476 a h
  have h4 : Entails.eval a c2477 := derived2477 a h
  have h5 : Entails.eval a c2480 := derived2480 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c2482 := derived2482 a h
  have h8 : Entails.eval a c2469 := derived2469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2484 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c363, some c156, some c2167, some c2261, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2484 : lratChecker f2484 p2484 = .success := by decide +kernel
theorem unsat2484 : Unsatisfiable (PosFin 57) f2484 := by
  apply lratCheckerSound f2484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2484
  · intro a ha; simp [p2484] at ha; subst a; trivial
  · exact checked2484
theorem derived2484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2484 := by
  apply localUnsat_implies_entails f2484 [c363, c156, c2167, c2261] c2484 unsat2484 (by rfl) a
  have h0 : Entails.eval a c363 := h 362 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c2167 := derived2167 a h
  have h3 : Entails.eval a c2261 := derived2261 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2485 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2456, some c2357, some c2484, some c2203, some c1039, some c362, some c2167, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2485 : lratChecker f2485 p2485 = .success := by decide +kernel
theorem unsat2485 : Unsatisfiable (PosFin 57) f2485 := by
  apply lratCheckerSound f2485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2485
  · intro a ha; simp [p2485] at ha; subst a; trivial
  · exact checked2485
theorem derived2485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2485 := by
  apply localUnsat_implies_entails f2485 [c2456, c2357, c2484, c2203, c1039, c362, c2167] c2485 unsat2485 (by rfl) a
  have h0 : Entails.eval a c2456 := derived2456 a h
  have h1 : Entails.eval a c2357 := derived2357 a h
  have h2 : Entails.eval a c2484 := derived2484 a h
  have h3 : Entails.eval a c2203 := derived2203 a h
  have h4 : Entails.eval a c1039 := derived1039 a h
  have h5 : Entails.eval a c362 := h 361 (by decide)
  have h6 : Entails.eval a c2167 := derived2167 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2486 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨33, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c314, some c313, some c2238, some c2060, some c2059, some c270, some c284, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2486 : lratChecker f2486 p2486 = .success := by decide +kernel
theorem unsat2486 : Unsatisfiable (PosFin 57) f2486 := by
  apply lratCheckerSound f2486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2486
  · intro a ha; simp [p2486] at ha; subst a; trivial
  · exact checked2486
theorem derived2486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2486 := by
  apply localUnsat_implies_entails f2486 [c2455, c314, c313, c2238, c2060, c2059, c270, c284] c2486 unsat2486 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c314 := h 313 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c2238 := derived2238 a h
  have h4 : Entails.eval a c2060 := derived2060 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2487 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2093, some c2357, some c67, some c79, some c2485, some c369, some c66, some c2097, some c376, some c2486, some c153, some c2393, some c2094, some c1480, some c2332, some c163, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2487 : lratChecker f2487 p2487 = .success := by decide +kernel
theorem unsat2487 : Unsatisfiable (PosFin 57) f2487 := by
  apply lratCheckerSound f2487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2487
  · intro a ha; simp [p2487] at ha; subst a; trivial
  · exact checked2487
theorem derived2487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2487 := by
  apply localUnsat_implies_entails f2487 [c2093, c2357, c67, c79, c2485, c369, c66, c2097, c376, c2486, c153, c2393, c2094, c1480, c2332, c163] c2487 unsat2487 (by rfl) a
  have h0 : Entails.eval a c2093 := derived2093 a h
  have h1 : Entails.eval a c2357 := derived2357 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c2485 := derived2485 a h
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c2097 := derived2097 a h
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c2486 := derived2486 a h
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c2393 := derived2393 a h
  have h12 : Entails.eval a c2094 := derived2094 a h
  have h13 : Entails.eval a c1480 := derived1480 a h
  have h14 : Entails.eval a c2332 := derived2332 a h
  have h15 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2488 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2483, some c104, some c2357, some c2093, some c2456, some c2487, some c371, some c1287, some c2479, some c153, some c2094, some c363, some c292, some c14, some c155, some c2241, some c2297, some c2100, some c275, some c195, some c231, some c32, some c864, some c203, some c111, some c126, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2488 : lratChecker f2488 p2488 = .success := by decide +kernel
theorem unsat2488 : Unsatisfiable (PosFin 57) f2488 := by
  apply lratCheckerSound f2488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2488
  · intro a ha; simp [p2488] at ha; subst a; trivial
  · exact checked2488
theorem derived2488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2488 := by
  apply localUnsat_implies_entails f2488 [c2201, c2483, c104, c2357, c2093, c2456, c2487, c371, c1287, c2479, c153, c2094, c363, c292, c14, c155, c2241, c2297, c2100, c275, c195, c231, c32, c864, c203, c111, c126] c2488 unsat2488 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2483 := derived2483 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2357 := derived2357 a h
  have h4 : Entails.eval a c2093 := derived2093 a h
  have h5 : Entails.eval a c2456 := derived2456 a h
  have h6 : Entails.eval a c2487 := derived2487 a h
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c2479 := derived2479 a h
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c2094 := derived2094 a h
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c2241 := derived2241 a h
  have h17 : Entails.eval a c2297 := derived2297 a h
  have h18 : Entails.eval a c2100 := derived2100 a h
  have h19 : Entails.eval a c275 := h 274 (by decide)
  have h20 : Entails.eval a c195 := h 194 (by decide)
  have h21 : Entails.eval a c231 := h 230 (by decide)
  have h22 : Entails.eval a c32 := h 31 (by decide)
  have h23 : Entails.eval a c864 := derived864 a h
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c111 := h 110 (by decide)
  have h26 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2489 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2025, some c2059, some c314, some c285, some c38, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2489 : lratChecker f2489 p2489 = .success := by decide +kernel
theorem unsat2489 : Unsatisfiable (PosFin 57) f2489 := by
  apply lratCheckerSound f2489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2489
  · intro a ha; simp [p2489] at ha; subst a; trivial
  · exact checked2489
theorem derived2489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2489 := by
  apply localUnsat_implies_entails f2489 [c2455, c2025, c2059, c314, c285, c38] c2489 unsat2489 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2025 := derived2025 a h
  have h2 : Entails.eval a c2059 := derived2059 a h
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2490 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨44, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2489, some c274, some c38, some c325, some c314, some c2033, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2490 : lratChecker f2490 p2490 = .success := by decide +kernel
theorem unsat2490 : Unsatisfiable (PosFin 57) f2490 := by
  apply lratCheckerSound f2490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2490
  · intro a ha; simp [p2490] at ha; subst a; trivial
  · exact checked2490
theorem derived2490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2490 := by
  apply localUnsat_implies_entails f2490 [c2455, c2489, c274, c38, c325, c314, c2033] c2490 unsat2490 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2489 := derived2489 a h
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2491 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2027, some c79, some c102, some c78, some c2490, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2491 : lratChecker f2491 p2491 = .success := by decide +kernel
theorem unsat2491 : Unsatisfiable (PosFin 57) f2491 := by
  apply lratCheckerSound f2491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2491
  · intro a ha; simp [p2491] at ha; subst a; trivial
  · exact checked2491
theorem derived2491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2491 := by
  apply localUnsat_implies_entails f2491 [c2027, c79, c102, c78, c2490] c2491 unsat2491 (by rfl) a
  have h0 : Entails.eval a c2027 := derived2027 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c2490 := derived2490 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2492 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2483, some c104, some c2488, some c2491, some c368, some c371, some c1287, some c2479, some c2393, some c363, some c2466, some c292, some c362, some c1128, some c2469, some c102, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2492 : lratChecker f2492 p2492 = .success := by decide +kernel
theorem unsat2492 : Unsatisfiable (PosFin 57) f2492 := by
  apply lratCheckerSound f2492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2492
  · intro a ha; simp [p2492] at ha; subst a; trivial
  · exact checked2492
theorem derived2492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2492 := by
  apply localUnsat_implies_entails f2492 [c2201, c2455, c2483, c104, c2488, c2491, c368, c371, c1287, c2479, c2393, c363, c2466, c292, c362, c1128, c2469, c102] c2492 unsat2492 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2483 := derived2483 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2488 := derived2488 a h
  have h5 : Entails.eval a c2491 := derived2491 a h
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c2479 := derived2479 a h
  have h10 : Entails.eval a c2393 := derived2393 a h
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c2466 := derived2466 a h
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c362 := h 361 (by decide)
  have h15 : Entails.eval a c1128 := derived1128 a h
  have h16 : Entails.eval a c2469 := derived2469 a h
  have h17 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2493 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c1241, some c156, some c162, some c2261, some c1480, some c2167, some c166, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2493 : lratChecker f2493 p2493 = .success := by decide +kernel
theorem unsat2493 : Unsatisfiable (PosFin 57) f2493 := by
  apply lratCheckerSound f2493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2493
  · intro a ha; simp [p2493] at ha; subst a; trivial
  · exact checked2493
theorem derived2493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2493 := by
  apply localUnsat_implies_entails f2493 [c79, c1241, c156, c162, c2261, c1480, c2167, c166] c2493 unsat2493 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c1241 := derived1241 a h
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c2261 := derived2261 a h
  have h5 : Entails.eval a c1480 := derived1480 a h
  have h6 : Entails.eval a c2167 := derived2167 a h
  have h7 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2494 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c2456, some c2357, some c2493, some c2203, some c1039, some c2332, some c2167, some c163, some c167, some c1480, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2494 : lratChecker f2494 p2494 = .success := by decide +kernel
theorem unsat2494 : Unsatisfiable (PosFin 57) f2494 := by
  apply lratCheckerSound f2494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2494
  · intro a ha; simp [p2494] at ha; subst a; trivial
  · exact checked2494
theorem derived2494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2494 := by
  apply localUnsat_implies_entails f2494 [c79, c2456, c2357, c2493, c2203, c1039, c2332, c2167, c163, c167, c1480] c2494 unsat2494 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c2456 := derived2456 a h
  have h2 : Entails.eval a c2357 := derived2357 a h
  have h3 : Entails.eval a c2493 := derived2493 a h
  have h4 : Entails.eval a c2203 := derived2203 a h
  have h5 : Entails.eval a c1039 := derived1039 a h
  have h6 : Entails.eval a c2332 := derived2332 a h
  have h7 : Entails.eval a c2167 := derived2167 a h
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c1480 := derived1480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2495 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c298, some c289, some c2047, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2495 : lratChecker f2495 p2495 = .success := by decide +kernel
theorem unsat2495 : Unsatisfiable (PosFin 57) f2495 := by
  apply lratCheckerSound f2495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2495
  · intro a ha; simp [p2495] at ha; subst a; trivial
  · exact checked2495
theorem derived2495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2495 := by
  apply localUnsat_implies_entails f2495 [c298, c289, c2047] c2495 unsat2495 (by rfl) a
  have h0 : Entails.eval a c298 := h 297 (by decide)
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c2047 := derived2047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2496 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2456, some c2093, some c2230, some c67, some c379, some c2494, some c369, some c66, some c2097, some c314, some c329, some c2495, some c270, some c2060, some c274, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2496 : lratChecker f2496 p2496 = .success := by decide +kernel
theorem unsat2496 : Unsatisfiable (PosFin 57) f2496 := by
  apply lratCheckerSound f2496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2496
  · intro a ha; simp [p2496] at ha; subst a; trivial
  · exact checked2496
theorem derived2496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2496 := by
  apply localUnsat_implies_entails f2496 [c2455, c2456, c2093, c2230, c67, c379, c2494, c369, c66, c2097, c314, c329, c2495, c270, c2060, c274] c2496 unsat2496 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2456 := derived2456 a h
  have h2 : Entails.eval a c2093 := derived2093 a h
  have h3 : Entails.eval a c2230 := derived2230 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c2494 := derived2494 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c2097 := derived2097 a h
  have h10 : Entails.eval a c314 := h 313 (by decide)
  have h11 : Entails.eval a c329 := h 328 (by decide)
  have h12 : Entails.eval a c2495 := derived2495 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c2060 := derived2060 a h
  have h15 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2497 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2205, some c2241, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2497 : lratChecker f2497 p2497 = .success := by decide +kernel
theorem unsat2497 : Unsatisfiable (PosFin 57) f2497 := by
  apply lratCheckerSound f2497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2497
  · intro a ha; simp [p2497] at ha; subst a; trivial
  · exact checked2497
theorem derived2497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2497 := by
  apply localUnsat_implies_entails f2497 [c2205, c2241] c2497 unsat2497 (by rfl) a
  have h0 : Entails.eval a c2205 := derived2205 a h
  have h1 : Entails.eval a c2241 := derived2241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2498 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨25, by decide⟩, false), (⟨45, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2456, some c2357, some c2230, some c1241, some c156, some c2320, some c166, some c2261, some c377, some c290, some c1480, some c2100, some c275, some c1237, some c272, some c2097, some c330, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2498 : lratChecker f2498 p2498 = .success := by decide +kernel
theorem unsat2498 : Unsatisfiable (PosFin 57) f2498 := by
  apply lratCheckerSound f2498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2498
  · intro a ha; simp [p2498] at ha; subst a; trivial
  · exact checked2498
theorem derived2498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2498 := by
  apply localUnsat_implies_entails f2498 [c2456, c2357, c2230, c1241, c156, c2320, c166, c2261, c377, c290, c1480, c2100, c275, c1237, c272, c2097, c330] c2498 unsat2498 (by rfl) a
  have h0 : Entails.eval a c2456 := derived2456 a h
  have h1 : Entails.eval a c2357 := derived2357 a h
  have h2 : Entails.eval a c2230 := derived2230 a h
  have h3 : Entails.eval a c1241 := derived1241 a h
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c2320 := derived2320 a h
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c2261 := derived2261 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c1480 := derived1480 a h
  have h11 : Entails.eval a c2100 := derived2100 a h
  have h12 : Entails.eval a c275 := h 274 (by decide)
  have h13 : Entails.eval a c1237 := derived1237 a h
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c2097 := derived2097 a h
  have h16 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2499 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c2483, some c2492, some c2496, some c368, some c66, some c2497, some c2456, some c2479, some c289, some c371, some c2093, some c2498, some c1039, some c2136, some c2100, some c275, some c864, some c195, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2499 : lratChecker f2499 p2499 = .success := by decide +kernel
theorem unsat2499 : Unsatisfiable (PosFin 57) f2499 := by
  apply lratCheckerSound f2499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2499
  · intro a ha; simp [p2499] at ha; subst a; trivial
  · exact checked2499
theorem derived2499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2499 := by
  apply localUnsat_implies_entails f2499 [c2201, c104, c2483, c2492, c2496, c368, c66, c2497, c2456, c2479, c289, c371, c2093, c2498, c1039, c2136, c2100, c275, c864, c195] c2499 unsat2499 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c2483 := derived2483 a h
  have h3 : Entails.eval a c2492 := derived2492 a h
  have h4 : Entails.eval a c2496 := derived2496 a h
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c2497 := derived2497 a h
  have h8 : Entails.eval a c2456 := derived2456 a h
  have h9 : Entails.eval a c2479 := derived2479 a h
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c2093 := derived2093 a h
  have h13 : Entails.eval a c2498 := derived2498 a h
  have h14 : Entails.eval a c1039 := derived1039 a h
  have h15 : Entails.eval a c2136 := derived2136 a h
  have h16 : Entails.eval a c2100 := derived2100 a h
  have h17 : Entails.eval a c275 := h 274 (by decide)
  have h18 : Entails.eval a c864 := derived864 a h
  have h19 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2500 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c325, some c314, some c2033, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2500 : lratChecker f2500 p2500 = .success := by decide +kernel
theorem unsat2500 : Unsatisfiable (PosFin 57) f2500 := by
  apply lratCheckerSound f2500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2500
  · intro a ha; simp [p2500] at ha; subst a; trivial
  · exact checked2500
theorem derived2500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2500 := by
  apply localUnsat_implies_entails f2500 [c2455, c325, c314, c2033] c2500 unsat2500 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2501 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2492, some c2483, some c104, some c2093, some c2456, some c2496, some c2479, some c289, some c2499, some c274, some c2500, some c270, some c329, some c2050, some c2026, some c2033, some c348, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2501 : lratChecker f2501 p2501 = .success := by decide +kernel
theorem unsat2501 : Unsatisfiable (PosFin 57) f2501 := by
  apply lratCheckerSound f2501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2501
  · intro a ha; simp [p2501] at ha; subst a; trivial
  · exact checked2501
theorem derived2501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2501 := by
  apply localUnsat_implies_entails f2501 [c2201, c2455, c2492, c2483, c104, c2093, c2456, c2496, c2479, c289, c2499, c274, c2500, c270, c329, c2050, c2026, c2033, c348] c2501 unsat2501 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2492 := derived2492 a h
  have h3 : Entails.eval a c2483 := derived2483 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2093 := derived2093 a h
  have h6 : Entails.eval a c2456 := derived2456 a h
  have h7 : Entails.eval a c2496 := derived2496 a h
  have h8 : Entails.eval a c2479 := derived2479 a h
  have h9 : Entails.eval a c289 := h 288 (by decide)
  have h10 : Entails.eval a c2499 := derived2499 a h
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c2500 := derived2500 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c329 := h 328 (by decide)
  have h15 : Entails.eval a c2050 := derived2050 a h
  have h16 : Entails.eval a c2026 := derived2026 a h
  have h17 : Entails.eval a c2033 := derived2033 a h
  have h18 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2502 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2037, some c2036, some c379, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2502 : lratChecker f2502 p2502 = .success := by decide +kernel
theorem unsat2502 : Unsatisfiable (PosFin 57) f2502 := by
  apply lratCheckerSound f2502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2502
  · intro a ha; simp [p2502] at ha; subst a; trivial
  · exact checked2502
theorem derived2502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2502 := by
  apply localUnsat_implies_entails f2502 [c2455, c2037, c2036, c379] c2502 unsat2502 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c2036 := derived2036 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2503 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2479, some c72, some c1128, some c292, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2503 : lratChecker f2503 p2503 = .success := by decide +kernel
theorem unsat2503 : Unsatisfiable (PosFin 57) f2503 := by
  apply lratCheckerSound f2503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2503
  · intro a ha; simp [p2503] at ha; subst a; trivial
  · exact checked2503
theorem derived2503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2503 := by
  apply localUnsat_implies_entails f2503 [c2455, c2479, c72, c1128, c292] c2503 unsat2503 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2479 := derived2479 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1128 := derived1128 a h
  have h4 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2504 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2048, some c2045, some c281, some c321, some c36, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2504 : lratChecker f2504 p2504 = .success := by decide +kernel
theorem unsat2504 : Unsatisfiable (PosFin 57) f2504 := by
  apply lratCheckerSound f2504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2504
  · intro a ha; simp [p2504] at ha; subst a; trivial
  · exact checked2504
theorem derived2504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2504 := by
  apply localUnsat_implies_entails f2504 [c2455, c2048, c2045, c281, c321, c36] c2504 unsat2504 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2048 := derived2048 a h
  have h2 : Entails.eval a c2045 := derived2045 a h
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2505 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2504, some c2469, some c70, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2505 : lratChecker f2505 p2505 = .success := by decide +kernel
theorem unsat2505 : Unsatisfiable (PosFin 57) f2505 := by
  apply lratCheckerSound f2505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2505
  · intro a ha; simp [p2505] at ha; subst a; trivial
  · exact checked2505
theorem derived2505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2505 := by
  apply localUnsat_implies_entails f2505 [c2504, c2469, c70] c2505 unsat2505 (by rfl) a
  have h0 : Entails.eval a c2504 := derived2504 a h
  have h1 : Entails.eval a c2469 := derived2469 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2506 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c2483, some c2492, some c2501, some c2491, some c2502, some c2503, some c102, some c2505, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2506 : lratChecker f2506 p2506 = .success := by decide +kernel
theorem unsat2506 : Unsatisfiable (PosFin 57) f2506 := by
  apply lratCheckerSound f2506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2506
  · intro a ha; simp [p2506] at ha; subst a; trivial
  · exact checked2506
theorem derived2506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2506 := by
  apply localUnsat_implies_entails f2506 [c2201, c104, c2483, c2492, c2501, c2491, c2502, c2503, c102, c2505] c2506 unsat2506 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c2483 := derived2483 a h
  have h3 : Entails.eval a c2492 := derived2492 a h
  have h4 : Entails.eval a c2501 := derived2501 a h
  have h5 : Entails.eval a c2491 := derived2491 a h
  have h6 : Entails.eval a c2502 := derived2502 a h
  have h7 : Entails.eval a c2503 := derived2503 a h
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c2505 := derived2505 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2507 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2059, some c2047, some c2061, some c308, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2507 : lratChecker f2507 p2507 = .success := by decide +kernel
theorem unsat2507 : Unsatisfiable (PosFin 57) f2507 := by
  apply lratCheckerSound f2507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2507
  · intro a ha; simp [p2507] at ha; subst a; trivial
  · exact checked2507
theorem derived2507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2507 := by
  apply localUnsat_implies_entails f2507 [c2455, c2059, c2047, c2061, c308] c2507 unsat2507 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2059 := derived2059 a h
  have h2 : Entails.eval a c2047 := derived2047 a h
  have h3 : Entails.eval a c2061 := derived2061 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2508 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c290, some c2323, some c952, some c2050, some c196, some c320, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2508 : lratChecker f2508 p2508 = .success := by decide +kernel
theorem unsat2508 : Unsatisfiable (PosFin 57) f2508 := by
  apply lratCheckerSound f2508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2508
  · intro a ha; simp [p2508] at ha; subst a; trivial
  · exact checked2508
theorem derived2508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2508 := by
  apply localUnsat_implies_entails f2508 [c2201, c290, c2323, c952, c2050, c196, c320] c2508 unsat2508 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c2323 := derived2323 a h
  have h3 : Entails.eval a c952 := derived952 a h
  have h4 : Entails.eval a c2050 := derived2050 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2509 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c104, some c2507, some c2506, some c68, some c376, some c66, some c2456, some c2357, some c379, some c2032, some c367, some c366, some c2204, some c1982, some c2261, some c1039, some c179, some c14, some c164, some c155, some c168, some c185, some c1972, some c2508, some c362, some c273, some c864, some c195, some c331, some c339, some c2026, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked2509 : lratChecker f2509 p2509 = .success := by decide +kernel
theorem unsat2509 : Unsatisfiable (PosFin 57) f2509 := by
  apply lratCheckerSound f2509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2509
  · intro a ha; simp [p2509] at ha; subst a; trivial
  · exact checked2509
theorem derived2509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2509 := by
  apply localUnsat_implies_entails f2509 [c2455, c2201, c104, c2507, c2506, c68, c376, c66, c2456, c2357, c379, c2032, c367, c366, c2204, c1982, c2261, c1039, c179, c14, c164, c155, c168, c185, c1972, c2508, c362, c273, c864, c195, c331, c339, c2026] c2509 unsat2509 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2507 := derived2507 a h
  have h4 : Entails.eval a c2506 := derived2506 a h
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c2456 := derived2456 a h
  have h9 : Entails.eval a c2357 := derived2357 a h
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c2032 := derived2032 a h
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c2204 := derived2204 a h
  have h15 : Entails.eval a c1982 := derived1982 a h
  have h16 : Entails.eval a c2261 := derived2261 a h
  have h17 : Entails.eval a c1039 := derived1039 a h
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c164 := h 163 (by decide)
  have h21 : Entails.eval a c155 := h 154 (by decide)
  have h22 : Entails.eval a c168 := h 167 (by decide)
  have h23 : Entails.eval a c185 := h 184 (by decide)
  have h24 : Entails.eval a c1972 := derived1972 a h
  have h25 : Entails.eval a c2508 := derived2508 a h
  have h26 : Entails.eval a c362 := h 361 (by decide)
  have h27 : Entails.eval a c273 := h 272 (by decide)
  have h28 : Entails.eval a c864 := derived864 a h
  have h29 : Entails.eval a c195 := h 194 (by decide)
  have h30 : Entails.eval a c331 := h 330 (by decide)
  have h31 : Entails.eval a c339 := h 338 (by decide)
  have h32 : Entails.eval a c2026 := derived2026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2510 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2050, some c2026, some c2033, some c348, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2510 : lratChecker f2510 p2510 = .success := by decide +kernel
theorem unsat2510 : Unsatisfiable (PosFin 57) f2510 := by
  apply lratCheckerSound f2510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2510
  · intro a ha; simp [p2510] at ha; subst a; trivial
  · exact checked2510
theorem derived2510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2510 := by
  apply localUnsat_implies_entails f2510 [c2455, c2050, c2026, c2033, c348] c2510 unsat2510 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2050 := derived2050 a h
  have h2 : Entails.eval a c2026 := derived2026 a h
  have h3 : Entails.eval a c2033 := derived2033 a h
  have h4 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2511 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨33, by decide⟩, false), (⟨46, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c313, some c2238, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2511 : lratChecker f2511 p2511 = .success := by decide +kernel
theorem unsat2511 : Unsatisfiable (PosFin 57) f2511 := by
  apply lratCheckerSound f2511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2511
  · intro a ha; simp [p2511] at ha; subst a; trivial
  · exact checked2511
theorem derived2511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2511 := by
  apply localUnsat_implies_entails f2511 [c314, c313, c2238] c2511 unsat2511 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c2238 := derived2238 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2512 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c68, some c379, some c2032, some c104, some c2357, some c2456, some c2507, some c2509, some c81, some c2485, some c274, some c2510, some c314, some c194, some c31, some c2511, some c363, some c292, some c332, some c196, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2512 : lratChecker f2512 p2512 = .success := by decide +kernel
theorem unsat2512 : Unsatisfiable (PosFin 57) f2512 := by
  apply lratCheckerSound f2512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2512
  · intro a ha; simp [p2512] at ha; subst a; trivial
  · exact checked2512
theorem derived2512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2512 := by
  apply localUnsat_implies_entails f2512 [c2201, c2455, c2506, c68, c379, c2032, c104, c2357, c2456, c2507, c2509, c81, c2485, c274, c2510, c314, c194, c31, c2511, c363, c292, c332, c196] c2512 unsat2512 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c2032 := derived2032 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c2357 := derived2357 a h
  have h8 : Entails.eval a c2456 := derived2456 a h
  have h9 : Entails.eval a c2507 := derived2507 a h
  have h10 : Entails.eval a c2509 := derived2509 a h
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c2485 := derived2485 a h
  have h13 : Entails.eval a c274 := h 273 (by decide)
  have h14 : Entails.eval a c2510 := derived2510 a h
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c194 := h 193 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c2511 := derived2511 a h
  have h19 : Entails.eval a c363 := h 362 (by decide)
  have h20 : Entails.eval a c292 := h 291 (by decide)
  have h21 : Entails.eval a c332 := h 331 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2513 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨51, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c68, some c104, some c2059, some c2047, some c297, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2513 : lratChecker f2513 p2513 = .success := by decide +kernel
theorem unsat2513 : Unsatisfiable (PosFin 57) f2513 := by
  apply lratCheckerSound f2513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2513
  · intro a ha; simp [p2513] at ha; subst a; trivial
  · exact checked2513
theorem derived2513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2513 := by
  apply localUnsat_implies_entails f2513 [c2201, c2455, c2506, c68, c104, c2059, c2047, c297] c2513 unsat2513 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2047 := derived2047 a h
  have h7 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2514 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c2032, some c68, some c104, some c67, some c2512, some c2477, some c81, some c102, some c78, some c2513, some c274, some c46, some c38, some c297, some c314, some c36, some c2026, some c337, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2514 : lratChecker f2514 p2514 = .success := by decide +kernel
theorem unsat2514 : Unsatisfiable (PosFin 57) f2514 := by
  apply lratCheckerSound f2514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2514
  · intro a ha; simp [p2514] at ha; subst a; trivial
  · exact checked2514
theorem derived2514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2514 := by
  apply localUnsat_implies_entails f2514 [c2201, c2455, c2506, c2032, c68, c104, c67, c2512, c2477, c81, c102, c78, c2513, c274, c46, c38, c297, c314, c36, c2026, c337] c2514 unsat2514 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c2512 := derived2512 a h
  have h8 : Entails.eval a c2477 := derived2477 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c2513 := derived2513 a h
  have h13 : Entails.eval a c274 := h 273 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c2026 := derived2026 a h
  have h20 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2515 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false), (⟨6, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2032, some c367, some c366, some c276, some c316, some c1039, some c1118, some c40, some c1491, some c2261, some c179, some c289, some c2462, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2515 : lratChecker f2515 p2515 = .success := by decide +kernel
theorem unsat2515 : Unsatisfiable (PosFin 57) f2515 := by
  apply lratCheckerSound f2515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2515
  · intro a ha; simp [p2515] at ha; subst a; trivial
  · exact checked2515
theorem derived2515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2515 := by
  apply localUnsat_implies_entails f2515 [c2455, c2032, c367, c366, c276, c316, c1039, c1118, c40, c1491, c2261, c179, c289, c2462] c2515 unsat2515 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2032 := derived2032 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c1039 := derived1039 a h
  have h7 : Entails.eval a c1118 := derived1118 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c1491 := derived1491 a h
  have h10 : Entails.eval a c2261 := derived2261 a h
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c2462 := derived2462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2516 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c2506, some c104, some c2357, some c2456, some c2507, some c2510, some c2512, some c2515, some c81, some c2514, some c2032, some c68, some c2485, some c2030, some c289, some c193, some c30, some c2071, some c1039, some c2261, some c156, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2516 : lratChecker f2516 p2516 = .success := by decide +kernel
theorem unsat2516 : Unsatisfiable (PosFin 57) f2516 := by
  apply lratCheckerSound f2516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2516
  · intro a ha; simp [p2516] at ha; subst a; trivial
  · exact checked2516
theorem derived2516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2516 := by
  apply localUnsat_implies_entails f2516 [c2455, c2201, c2506, c104, c2357, c2456, c2507, c2510, c2512, c2515, c81, c2514, c2032, c68, c2485, c2030, c289, c193, c30, c2071, c1039, c2261, c156] c2516 unsat2516 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2357 := derived2357 a h
  have h5 : Entails.eval a c2456 := derived2456 a h
  have h6 : Entails.eval a c2507 := derived2507 a h
  have h7 : Entails.eval a c2510 := derived2510 a h
  have h8 : Entails.eval a c2512 := derived2512 a h
  have h9 : Entails.eval a c2515 := derived2515 a h
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c2514 := derived2514 a h
  have h12 : Entails.eval a c2032 := derived2032 a h
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c2485 := derived2485 a h
  have h15 : Entails.eval a c2030 := derived2030 a h
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  have h18 : Entails.eval a c30 := h 29 (by decide)
  have h19 : Entails.eval a c2071 := derived2071 a h
  have h20 : Entails.eval a c1039 := derived1039 a h
  have h21 : Entails.eval a c2261 := derived2261 a h
  have h22 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2517 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c2032, some c68, some c104, some c2357, some c2456, some c2507, some c2510, some c2512, some c2515, some c81, some c2516, some c274, some c314, some c2511, some c194, some c2094, some c2331, some c31, some c2320, some c292, some c332, some c196, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2517 : lratChecker f2517 p2517 = .success := by decide +kernel
theorem unsat2517 : Unsatisfiable (PosFin 57) f2517 := by
  apply lratCheckerSound f2517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2517
  · intro a ha; simp [p2517] at ha; subst a; trivial
  · exact checked2517
theorem derived2517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2517 := by
  apply localUnsat_implies_entails f2517 [c2201, c2455, c2506, c2032, c68, c104, c2357, c2456, c2507, c2510, c2512, c2515, c81, c2516, c274, c314, c2511, c194, c2094, c2331, c31, c2320, c292, c332, c196] c2517 unsat2517 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c2357 := derived2357 a h
  have h7 : Entails.eval a c2456 := derived2456 a h
  have h8 : Entails.eval a c2507 := derived2507 a h
  have h9 : Entails.eval a c2510 := derived2510 a h
  have h10 : Entails.eval a c2512 := derived2512 a h
  have h11 : Entails.eval a c2515 := derived2515 a h
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c2516 := derived2516 a h
  have h14 : Entails.eval a c274 := h 273 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c2511 := derived2511 a h
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c2094 := derived2094 a h
  have h19 : Entails.eval a c2331 := derived2331 a h
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c2320 := derived2320 a h
  have h22 : Entails.eval a c292 := h 291 (by decide)
  have h23 : Entails.eval a c332 := h 331 (by decide)
  have h24 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2518 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c2032, some c366, some c367, some c68, some c104, some c2059, some c2513, some c2039, some c91, some c1039, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2518 : lratChecker f2518 p2518 = .success := by decide +kernel
theorem unsat2518 : Unsatisfiable (PosFin 57) f2518 := by
  apply lratCheckerSound f2518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2518
  · intro a ha; simp [p2518] at ha; subst a; trivial
  · exact checked2518
theorem derived2518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2518 := by
  apply localUnsat_implies_entails f2518 [c2201, c2455, c2506, c2032, c366, c367, c68, c104, c2059, c2513, c2039, c91, c1039] c2518 unsat2518 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c2059 := derived2059 a h
  have h9 : Entails.eval a c2513 := derived2513 a h
  have h10 : Entails.eval a c2039 := derived2039 a h
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c1039 := derived1039 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2519 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c2032, some c366, some c367, some c68, some c104, some c2518, some c276, some c47, some c40, some c49, some c316, some c297, some c2023, some c91, some c1039, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2519 : lratChecker f2519 p2519 = .success := by decide +kernel
theorem unsat2519 : Unsatisfiable (PosFin 57) f2519 := by
  apply lratCheckerSound f2519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2519
  · intro a ha; simp [p2519] at ha; subst a; trivial
  · exact checked2519
theorem derived2519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2519 := by
  apply localUnsat_implies_entails f2519 [c2201, c2455, c2506, c2032, c366, c367, c68, c104, c2518, c276, c47, c40, c49, c316, c297, c2023, c91, c1039] c2519 unsat2519 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c2518 := derived2518 a h
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c297 := h 296 (by decide)
  have h15 : Entails.eval a c2023 := derived2023 a h
  have h16 : Entails.eval a c91 := h 90 (by decide)
  have h17 : Entails.eval a c1039 := derived1039 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2520 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2506, some c2032, some c366, some c2517, some c2519, some c102, some c70, some c68, some c104, some c2025, some c2059, some c2513, some c2057, some c301, some c38, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2520 : lratChecker f2520 p2520 = .success := by decide +kernel
theorem unsat2520 : Unsatisfiable (PosFin 57) f2520 := by
  apply lratCheckerSound f2520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2520
  · intro a ha; simp [p2520] at ha; subst a; trivial
  · exact checked2520
theorem derived2520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2520 := by
  apply localUnsat_implies_entails f2520 [c2201, c2455, c2506, c2032, c366, c2517, c2519, c102, c70, c68, c104, c2025, c2059, c2513, c2057, c301, c38] c2520 unsat2520 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c2517 := derived2517 a h
  have h6 : Entails.eval a c2519 := derived2519 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c2025 := derived2025 a h
  have h12 : Entails.eval a c2059 := derived2059 a h
  have h13 : Entails.eval a c2513 := derived2513 a h
  have h14 : Entails.eval a c2057 := derived2057 a h
  have h15 : Entails.eval a c301 := h 300 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2521 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2032, some c366, some c367, some c168, some c164, some c185, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2521 : lratChecker f2521 p2521 = .success := by decide +kernel
theorem unsat2521 : Unsatisfiable (PosFin 57) f2521 := by
  apply lratCheckerSound f2521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2521
  · intro a ha; simp [p2521] at ha; subst a; trivial
  · exact checked2521
theorem derived2521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2521 := by
  apply localUnsat_implies_entails f2521 [c2455, c2032, c366, c367, c168, c164, c185] c2521 unsat2521 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2032 := derived2032 a h
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2522 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c2506, some c2032, some c2520, some c276, some c68, some c366, some c2517, some c2519, some c102, some c70, some c377, some c104, some c2023, some c2502, some c316, some c196, some c24, some c32, some c524, some c2521, some c14, some c153, some c273, some c313, some c271, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2522 : lratChecker f2522 p2522 = .success := by decide +kernel
theorem unsat2522 : Unsatisfiable (PosFin 57) f2522 := by
  apply lratCheckerSound f2522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2522
  · intro a ha; simp [p2522] at ha; subst a; trivial
  · exact checked2522
theorem derived2522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2522 := by
  apply localUnsat_implies_entails f2522 [c2455, c2201, c2506, c2032, c2520, c276, c68, c366, c2517, c2519, c102, c70, c377, c104, c2023, c2502, c316, c196, c24, c32, c524, c2521, c14, c153, c273, c313, c271] c2522 unsat2522 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c2520 := derived2520 a h
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c2517 := derived2517 a h
  have h9 : Entails.eval a c2519 := derived2519 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c2023 := derived2023 a h
  have h15 : Entails.eval a c2502 := derived2502 a h
  have h16 : Entails.eval a c316 := h 315 (by decide)
  have h17 : Entails.eval a c196 := h 195 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c32 := h 31 (by decide)
  have h20 : Entails.eval a c524 := derived524 a h
  have h21 : Entails.eval a c2521 := derived2521 a h
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c153 := h 152 (by decide)
  have h24 : Entails.eval a c273 := h 272 (by decide)
  have h25 : Entails.eval a c313 := h 312 (by decide)
  have h26 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2523 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2517, some c2506, some c2032, some c68, some c366, some c2519, some c102, some c70, some c2520, some c2522, some c290, some c38, some c330, some c341, some c2033, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2523 : lratChecker f2523 p2523 = .success := by decide +kernel
theorem unsat2523 : Unsatisfiable (PosFin 57) f2523 := by
  apply lratCheckerSound f2523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2523
  · intro a ha; simp [p2523] at ha; subst a; trivial
  · exact checked2523
theorem derived2523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2523 := by
  apply localUnsat_implies_entails f2523 [c2455, c2517, c2506, c2032, c68, c366, c2519, c102, c70, c2520, c2522, c290, c38, c330, c341, c2033] c2523 unsat2523 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2517 := derived2517 a h
  have h2 : Entails.eval a c2506 := derived2506 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c2519 := derived2519 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c2520 := derived2520 a h
  have h10 : Entails.eval a c2522 := derived2522 a h
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c330 := h 329 (by decide)
  have h14 : Entails.eval a c341 := h 340 (by decide)
  have h15 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2524 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c2517, some c2506, some c2523, some c81, some c102, some c68, some c104, some c2025, some c2059, some c2513, some c2057, some c90, some c38, some c301, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2524 : lratChecker f2524 p2524 = .success := by decide +kernel
theorem unsat2524 : Unsatisfiable (PosFin 57) f2524 := by
  apply lratCheckerSound f2524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2524
  · intro a ha; simp [p2524] at ha; subst a; trivial
  · exact checked2524
theorem derived2524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2524 := by
  apply localUnsat_implies_entails f2524 [c2201, c2455, c2517, c2506, c2523, c81, c102, c68, c104, c2025, c2059, c2513, c2057, c90, c38, c301] c2524 unsat2524 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2517 := derived2517 a h
  have h3 : Entails.eval a c2506 := derived2506 a h
  have h4 : Entails.eval a c2523 := derived2523 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c2025 := derived2025 a h
  have h10 : Entails.eval a c2059 := derived2059 a h
  have h11 : Entails.eval a c2513 := derived2513 a h
  have h12 : Entails.eval a c2057 := derived2057 a h
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2525 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨46, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c104, some c2502, some c2523, some c2506, some c2517, some c81, some c102, some c70, some c2376, some c363, some c156, some c2167, some c8, some c983, some c169, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2525 : lratChecker f2525 p2525 = .success := by decide +kernel
theorem unsat2525 : Unsatisfiable (PosFin 57) f2525 := by
  apply lratCheckerSound f2525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2525
  · intro a ha; simp [p2525] at ha; subst a; trivial
  · exact checked2525
theorem derived2525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2525 := by
  apply localUnsat_implies_entails f2525 [c2455, c2201, c104, c2502, c2523, c2506, c2517, c81, c102, c70, c2376, c363, c156, c2167, c8, c983, c169] c2525 unsat2525 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2502 := derived2502 a h
  have h4 : Entails.eval a c2523 := derived2523 a h
  have h5 : Entails.eval a c2506 := derived2506 a h
  have h6 : Entails.eval a c2517 := derived2517 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c2376 := derived2376 a h
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c156 := h 155 (by decide)
  have h13 : Entails.eval a c2167 := derived2167 a h
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c983 := derived983 a h
  have h16 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2526 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨49, by decide⟩, true), (⟨46, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c2525, some c104, some c2502, some c2523, some c2506, some c2517, some c81, some c102, some c70, some c2376, some c2514, some c14, some c16, some c172, some c165, some c185, some c184, some c1033, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2526 : lratChecker f2526 p2526 = .success := by decide +kernel
theorem unsat2526 : Unsatisfiable (PosFin 57) f2526 := by
  apply lratCheckerSound f2526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2526
  · intro a ha; simp [p2526] at ha; subst a; trivial
  · exact checked2526
theorem derived2526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2526 := by
  apply localUnsat_implies_entails f2526 [c2455, c2201, c2525, c104, c2502, c2523, c2506, c2517, c81, c102, c70, c2376, c2514, c14, c16, c172, c165, c185, c184, c1033] c2526 unsat2526 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2525 := derived2525 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2502 := derived2502 a h
  have h5 : Entails.eval a c2523 := derived2523 a h
  have h6 : Entails.eval a c2506 := derived2506 a h
  have h7 : Entails.eval a c2517 := derived2517 a h
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c2376 := derived2376 a h
  have h12 : Entails.eval a c2514 := derived2514 a h
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c172 := h 171 (by decide)
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c185 := h 184 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c1033 := derived1033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2527 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨46, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2201, some c2523, some c2506, some c2517, some c81, some c102, some c70, some c2376, some c2514, some c2032, some c104, some c2023, some c2502, some c2525, some c841, some c2526, some c155, some c173, some c2167, some c2071, some c8, some c153, some c231, some c32, some c165, some c111, some c187, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2527 : lratChecker f2527 p2527 = .success := by decide +kernel
theorem unsat2527 : Unsatisfiable (PosFin 57) f2527 := by
  apply lratCheckerSound f2527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2527
  · intro a ha; simp [p2527] at ha; subst a; trivial
  · exact checked2527
theorem derived2527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2527 := by
  apply localUnsat_implies_entails f2527 [c2455, c2201, c2523, c2506, c2517, c81, c102, c70, c2376, c2514, c2032, c104, c2023, c2502, c2525, c841, c2526, c155, c173, c2167, c2071, c8, c153, c231, c32, c165, c111, c187] c2527 unsat2527 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2523 := derived2523 a h
  have h3 : Entails.eval a c2506 := derived2506 a h
  have h4 : Entails.eval a c2517 := derived2517 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c2376 := derived2376 a h
  have h9 : Entails.eval a c2514 := derived2514 a h
  have h10 : Entails.eval a c2032 := derived2032 a h
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c2023 := derived2023 a h
  have h13 : Entails.eval a c2502 := derived2502 a h
  have h14 : Entails.eval a c2525 := derived2525 a h
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c2526 := derived2526 a h
  have h17 : Entails.eval a c155 := h 154 (by decide)
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c2167 := derived2167 a h
  have h20 : Entails.eval a c2071 := derived2071 a h
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  have h23 : Entails.eval a c231 := h 230 (by decide)
  have h24 : Entails.eval a c32 := h 31 (by decide)
  have h25 : Entails.eval a c165 := h 164 (by decide)
  have h26 : Entails.eval a c111 := h 110 (by decide)
  have h27 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2528 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2524, some c2517, some c2506, some c2523, some c81, some c102, some c68, some c70, some c2527, some c290, some c38, some c330, some c341, some c2033, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2528 : lratChecker f2528 p2528 = .success := by decide +kernel
theorem unsat2528 : Unsatisfiable (PosFin 57) f2528 := by
  apply lratCheckerSound f2528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2528
  · intro a ha; simp [p2528] at ha; subst a; trivial
  · exact checked2528
theorem derived2528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2528 := by
  apply localUnsat_implies_entails f2528 [c2455, c2524, c2517, c2506, c2523, c81, c102, c68, c70, c2527, c290, c38, c330, c341, c2033] c2528 unsat2528 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2524 := derived2524 a h
  have h2 : Entails.eval a c2517 := derived2517 a h
  have h3 : Entails.eval a c2506 := derived2506 a h
  have h4 : Entails.eval a c2523 := derived2523 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c2527 := derived2527 a h
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2529 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2455, some c104, some c2506, some c68, some c2032, some c2517, some c2523, some c81, some c102, some c2524, some c2528, some c274, some c38, some c314, some c2026, some c2033, some c341, some c337, some c90, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p2529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2529 : lratChecker f2529 p2529 = .success := by decide +kernel
theorem unsat2529 : Unsatisfiable (PosFin 57) f2529 := by
  apply lratCheckerSound f2529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2529
  · intro a ha; simp [p2529] at ha; subst a; trivial
  · exact checked2529
theorem derived2529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2529 := by
  apply localUnsat_implies_entails f2529 [c2201, c2455, c104, c2506, c68, c2032, c2517, c2523, c81, c102, c2524, c2528, c274, c38, c314, c2026, c2033, c341, c337, c90] c2529 unsat2529 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2506 := derived2506 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c2032 := derived2032 a h
  have h6 : Entails.eval a c2517 := derived2517 a h
  have h7 : Entails.eval a c2523 := derived2523 a h
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c2524 := derived2524 a h
  have h11 : Entails.eval a c2528 := derived2528 a h
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c314 := h 313 (by decide)
  have h15 : Entails.eval a c2026 := derived2026 a h
  have h16 : Entails.eval a c2033 := derived2033 a h
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c337 := h 336 (by decide)
  have h19 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2530 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2035, some c2023, some c2037, some c2268, some c2502, some c2477, some c69, some c2373, some c313, some c282, some c37, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2530 : lratChecker f2530 p2530 = .success := by decide +kernel
theorem unsat2530 : Unsatisfiable (PosFin 57) f2530 := by
  apply lratCheckerSound f2530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2530
  · intro a ha; simp [p2530] at ha; subst a; trivial
  · exact checked2530
theorem derived2530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2530 := by
  apply localUnsat_implies_entails f2530 [c2455, c2529, c2035, c2023, c2037, c2268, c2502, c2477, c69, c2373, c313, c282, c37] c2530 unsat2530 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c2023 := derived2023 a h
  have h4 : Entails.eval a c2037 := derived2037 a h
  have h5 : Entails.eval a c2268 := derived2268 a h
  have h6 : Entails.eval a c2502 := derived2502 a h
  have h7 : Entails.eval a c2477 := derived2477 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c2373 := derived2373 a h
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2531 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c1629, some c1651, some c1646, some c292, some c332, some c2025, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2531 : lratChecker f2531 p2531 = .success := by decide +kernel
theorem unsat2531 : Unsatisfiable (PosFin 57) f2531 := by
  apply lratCheckerSound f2531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2531
  · intro a ha; simp [p2531] at ha; subst a; trivial
  · exact checked2531
theorem derived2531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2531 := by
  apply localUnsat_implies_entails f2531 [c2455, c2529, c1629, c1651, c1646, c292, c332, c2025] c2531 unsat2531 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1646 := derived1646 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c2025 := derived2025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2532 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c276, some c313, some c273, some c271, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p2532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2532 : lratChecker f2532 p2532 = .success := by decide +kernel
theorem unsat2532 : Unsatisfiable (PosFin 57) f2532 := by
  apply lratCheckerSound f2532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2532
  · intro a ha; simp [p2532] at ha; subst a; trivial
  · exact checked2532
theorem derived2532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2532 := by
  apply localUnsat_implies_entails f2532 [c316, c276, c313, c273, c271] c2532 unsat2532 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c276 := h 275 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2533 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2093, some c2032, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2533 : lratChecker f2533 p2533 = .success := by decide +kernel
theorem unsat2533 : Unsatisfiable (PosFin 57) f2533 := by
  apply lratCheckerSound f2533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2533
  · intro a ha; simp [p2533] at ha; subst a; trivial
  · exact checked2533
theorem derived2533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2533 := by
  apply localUnsat_implies_entails f2533 [c2455, c2093, c2032] c2533 unsat2533 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2093 := derived2093 a h
  have h2 : Entails.eval a c2032 := derived2032 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2534 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2530, some c2507, some c2510, some c2533, some c276, some c2532, some c69, some c289, some c2462, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2534 : lratChecker f2534 p2534 = .success := by decide +kernel
theorem unsat2534 : Unsatisfiable (PosFin 57) f2534 := by
  apply lratCheckerSound f2534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2534
  · intro a ha; simp [p2534] at ha; subst a; trivial
  · exact checked2534
theorem derived2534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2534 := by
  apply localUnsat_implies_entails f2534 [c2529, c2530, c2507, c2510, c2533, c276, c2532, c69, c289, c2462] c2534 unsat2534 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2530 := derived2530 a h
  have h2 : Entails.eval a c2507 := derived2507 a h
  have h3 : Entails.eval a c2510 := derived2510 a h
  have h4 : Entails.eval a c2533 := derived2533 a h
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c2532 := derived2532 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c2462 := derived2462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2535 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2530, some c2534, some c2477, some c2531, some c102, some c2505, some c2032, some c82, some c70, some c2043, some c2045, some c322, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2535 : lratChecker f2535 p2535 = .success := by decide +kernel
theorem unsat2535 : Unsatisfiable (PosFin 57) f2535 := by
  apply lratCheckerSound f2535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2535
  · intro a ha; simp [p2535] at ha; subst a; trivial
  · exact checked2535
theorem derived2535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2535 := by
  apply localUnsat_implies_entails f2535 [c2455, c2529, c2530, c2534, c2477, c2531, c102, c2505, c2032, c82, c70, c2043, c2045, c322] c2535 unsat2535 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2530 := derived2530 a h
  have h3 : Entails.eval a c2534 := derived2534 a h
  have h4 : Entails.eval a c2477 := derived2477 a h
  have h5 : Entails.eval a c2531 := derived2531 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c2505 := derived2505 a h
  have h8 : Entails.eval a c2032 := derived2032 a h
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c2043 := derived2043 a h
  have h12 : Entails.eval a c2045 := derived2045 a h
  have h13 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2536 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2530, some c2531, some c2534, some c2477, some c102, some c2505, some c2032, some c2535, some c366, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2536 : lratChecker f2536 p2536 = .success := by decide +kernel
theorem unsat2536 : Unsatisfiable (PosFin 57) f2536 := by
  apply lratCheckerSound f2536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2536
  · intro a ha; simp [p2536] at ha; subst a; trivial
  · exact checked2536
theorem derived2536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2536 := by
  apply localUnsat_implies_entails f2536 [c2455, c2530, c2531, c2534, c2477, c102, c2505, c2032, c2535, c366] c2536 unsat2536 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2530 := derived2530 a h
  have h2 : Entails.eval a c2531 := derived2531 a h
  have h3 : Entails.eval a c2534 := derived2534 a h
  have h4 : Entails.eval a c2477 := derived2477 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c2505 := derived2505 a h
  have h7 : Entails.eval a c2032 := derived2032 a h
  have h8 : Entails.eval a c2535 := derived2535 a h
  have h9 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2537 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2035, some c2023, some c2037, some c2502, some c69, some c313, some c37, some c273, some c2063, some c2039, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2537 : lratChecker f2537 p2537 = .success := by decide +kernel
theorem unsat2537 : Unsatisfiable (PosFin 57) f2537 := by
  apply lratCheckerSound f2537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2537
  · intro a ha; simp [p2537] at ha; subst a; trivial
  · exact checked2537
theorem derived2537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2537 := by
  apply localUnsat_implies_entails f2537 [c2529, c2455, c2035, c2023, c2037, c2502, c69, c313, c37, c273, c2063, c2039] c2537 unsat2537 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c2023 := derived2023 a h
  have h4 : Entails.eval a c2037 := derived2037 a h
  have h5 : Entails.eval a c2502 := derived2502 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c2063 := derived2063 a h
  have h11 : Entails.eval a c2039 := derived2039 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2538 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c289, some c329, some c37, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2538 : lratChecker f2538 p2538 = .success := by decide +kernel
theorem unsat2538 : Unsatisfiable (PosFin 57) f2538 := by
  apply lratCheckerSound f2538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2538
  · intro a ha; simp [p2538] at ha; subst a; trivial
  · exact checked2538
theorem derived2538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2538 := by
  apply localUnsat_implies_entails f2538 [c2529, c289, c329, c37] c2538 unsat2538 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2539 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2537, some c2531, some c2536, some c2507, some c2510, some c2538, some c69, some c2485, some c2511, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2539 : lratChecker f2539 p2539 = .success := by decide +kernel
theorem unsat2539 : Unsatisfiable (PosFin 57) f2539 := by
  apply lratCheckerSound f2539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2539
  · intro a ha; simp [p2539] at ha; subst a; trivial
  · exact checked2539
theorem derived2539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2539 := by
  apply localUnsat_implies_entails f2539 [c2529, c2537, c2531, c2536, c2507, c2510, c2538, c69, c2485, c2511] c2539 unsat2539 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2537 := derived2537 a h
  have h2 : Entails.eval a c2531 := derived2531 a h
  have h3 : Entails.eval a c2536 := derived2536 a h
  have h4 : Entails.eval a c2507 := derived2507 a h
  have h5 : Entails.eval a c2510 := derived2510 a h
  have h6 : Entails.eval a c2538 := derived2538 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c2485 := derived2485 a h
  have h9 : Entails.eval a c2511 := derived2511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2540 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2537, some c2025, some c2059, some c2047, some c311, some c37, some c313, some c329, some c69, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2540 : lratChecker f2540 p2540 = .success := by decide +kernel
theorem unsat2540 : Unsatisfiable (PosFin 57) f2540 := by
  apply lratCheckerSound f2540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2540
  · intro a ha; simp [p2540] at ha; subst a; trivial
  · exact checked2540
theorem derived2540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2540 := by
  apply localUnsat_implies_entails f2540 [c2455, c2529, c2537, c2025, c2059, c2047, c311, c37, c313, c329, c69] c2540 unsat2540 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2537 := derived2537 a h
  have h3 : Entails.eval a c2025 := derived2025 a h
  have h4 : Entails.eval a c2059 := derived2059 a h
  have h5 : Entails.eval a c2047 := derived2047 a h
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2541 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c289, some c273, some c69, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2541 : lratChecker f2541 p2541 = .success := by decide +kernel
theorem unsat2541 : Unsatisfiable (PosFin 57) f2541 := by
  apply lratCheckerSound f2541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2541
  · intro a ha; simp [p2541] at ha; subst a; trivial
  · exact checked2541
theorem derived2541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2541 := by
  apply localUnsat_implies_entails f2541 [c2529, c289, c273, c69] c2541 unsat2541 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2542 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2537, some c2531, some c2539, some c102, some c2540, some c2541, some c50, some c274, some c290, some c70, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2542 : lratChecker f2542 p2542 = .success := by decide +kernel
theorem unsat2542 : Unsatisfiable (PosFin 57) f2542 := by
  apply lratCheckerSound f2542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2542
  · intro a ha; simp [p2542] at ha; subst a; trivial
  · exact checked2542
theorem derived2542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2542 := by
  apply localUnsat_implies_entails f2542 [c2529, c2537, c2531, c2539, c102, c2540, c2541, c50, c274, c290, c70] c2542 unsat2542 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2537 := derived2537 a h
  have h2 : Entails.eval a c2531 := derived2531 a h
  have h3 : Entails.eval a c2539 := derived2539 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c2540 := derived2540 a h
  have h6 : Entails.eval a c2541 := derived2541 a h
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2543 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2531, some c2542, some c2533, some c2032, some c2027, some c102, some c2505, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2543 : lratChecker f2543 p2543 = .success := by decide +kernel
theorem unsat2543 : Unsatisfiable (PosFin 57) f2543 := by
  apply lratCheckerSound f2543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2543
  · intro a ha; simp [p2543] at ha; subst a; trivial
  · exact checked2543
theorem derived2543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2543 := by
  apply localUnsat_implies_entails f2543 [c2455, c2531, c2542, c2533, c2032, c2027, c102, c2505] c2543 unsat2543 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2531 := derived2531 a h
  have h2 : Entails.eval a c2542 := derived2542 a h
  have h3 : Entails.eval a c2533 := derived2533 a h
  have h4 : Entails.eval a c2032 := derived2032 a h
  have h5 : Entails.eval a c2027 := derived2027 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c2505 := derived2505 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2544 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2537, some c2543, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2544 : lratChecker f2544 p2544 = .success := by decide +kernel
theorem unsat2544 : Unsatisfiable (PosFin 57) f2544 := by
  apply lratCheckerSound f2544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2544
  · intro a ha; simp [p2544] at ha; subst a; trivial
  · exact checked2544
theorem derived2544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2544 := by
  apply localUnsat_implies_entails f2544 [c2537, c2543] c2544 unsat2544 (by rfl) a
  have h0 : Entails.eval a c2537 := derived2537 a h
  have h1 : Entails.eval a c2543 := derived2543 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2545 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2037, some c2066, some c2070, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2545 : lratChecker f2545 p2545 = .success := by decide +kernel
theorem unsat2545 : Unsatisfiable (PosFin 57) f2545 := by
  apply lratCheckerSound f2545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2545
  · intro a ha; simp [p2545] at ha; subst a; trivial
  · exact checked2545
theorem derived2545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2545 := by
  apply localUnsat_implies_entails f2545 [c2455, c2037, c2066, c2070] c2545 unsat2545 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c2066 := derived2066 a h
  have h3 : Entails.eval a c2070 := derived2070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2546 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2037, some c2035, some c2019, some c1007, some c69, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2546 : lratChecker f2546 p2546 = .success := by decide +kernel
theorem unsat2546 : Unsatisfiable (PosFin 57) f2546 := by
  apply lratCheckerSound f2546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2546
  · intro a ha; simp [p2546] at ha; subst a; trivial
  · exact checked2546
theorem derived2546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2546 := by
  apply localUnsat_implies_entails f2546 [c2455, c2529, c2037, c2035, c2019, c1007, c69] c2546 unsat2546 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2037 := derived2037 a h
  have h3 : Entails.eval a c2035 := derived2035 a h
  have h4 : Entails.eval a c2019 := derived2019 a h
  have h5 : Entails.eval a c1007 := derived1007 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2547 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2035, some c367, some c2545, some c2025, some c316, some c2546, some c102, some c2037, some c366, some c70, some c1387, some c377, some c2372, some c5, some c1118, some c1031, some c2059, some c82, some c313, some c37, some c311, some c62, some c185, some c134, some c139, some c212, some c221, some c198, some c107, some c245, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked2547 : lratChecker f2547 p2547 = .success := by decide +kernel
theorem unsat2547 : Unsatisfiable (PosFin 57) f2547 := by
  apply lratCheckerSound f2547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2547
  · intro a ha; simp [p2547] at ha; subst a; trivial
  · exact checked2547
theorem derived2547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2547 := by
  apply localUnsat_implies_entails f2547 [c2455, c2529, c2544, c2035, c367, c2545, c2025, c316, c2546, c102, c2037, c366, c70, c1387, c377, c2372, c5, c1118, c1031, c2059, c82, c313, c37, c311, c62, c185, c134, c139, c212, c221, c198, c107, c245] c2547 unsat2547 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2035 := derived2035 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2545 := derived2545 a h
  have h6 : Entails.eval a c2025 := derived2025 a h
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c2546 := derived2546 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c2037 := derived2037 a h
  have h11 : Entails.eval a c366 := h 365 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c1387 := derived1387 a h
  have h14 : Entails.eval a c377 := h 376 (by decide)
  have h15 : Entails.eval a c2372 := derived2372 a h
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c1118 := derived1118 a h
  have h18 : Entails.eval a c1031 := derived1031 a h
  have h19 : Entails.eval a c2059 := derived2059 a h
  have h20 : Entails.eval a c82 := h 81 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  have h22 : Entails.eval a c37 := h 36 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  have h24 : Entails.eval a c62 := h 61 (by decide)
  have h25 : Entails.eval a c185 := h 184 (by decide)
  have h26 : Entails.eval a c134 := h 133 (by decide)
  have h27 : Entails.eval a c139 := h 138 (by decide)
  have h28 : Entails.eval a c212 := h 211 (by decide)
  have h29 : Entails.eval a c221 := h 220 (by decide)
  have h30 : Entails.eval a c198 := h 197 (by decide)
  have h31 : Entails.eval a c107 := h 106 (by decide)
  have h32 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2548 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨37, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2037, some c2035, some c230, some c245, some c219, some c107, some c224, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2548 : lratChecker f2548 p2548 = .success := by decide +kernel
theorem unsat2548 : Unsatisfiable (PosFin 57) f2548 := by
  apply lratCheckerSound f2548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2548
  · intro a ha; simp [p2548] at ha; subst a; trivial
  · exact checked2548
theorem derived2548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2548 := by
  apply localUnsat_implies_entails f2548 [c2455, c2037, c2035, c230, c245, c219, c107, c224] c2548 unsat2548 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c230 := h 229 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2549 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, true), (⟨53, by decide⟩, true), (⟨37, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨28, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2035, some c367, some c1118, some c37, some c179, some c1985, some c128, some c2548, some c111, some c106, some c224, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2549 : lratChecker f2549 p2549 = .success := by decide +kernel
theorem unsat2549 : Unsatisfiable (PosFin 57) f2549 := by
  apply lratCheckerSound f2549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2549
  · intro a ha; simp [p2549] at ha; subst a; trivial
  · exact checked2549
theorem derived2549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2549 := by
  apply localUnsat_implies_entails f2549 [c2529, c2035, c367, c1118, c37, c179, c1985, c128, c2548, c111, c106, c224] c2549 unsat2549 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2035 := derived2035 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c1985 := derived1985 a h
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c2548 := derived2548 a h
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2550 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2201, some c2545, some c2059, some c2025, some c2037, some c2035, some c367, some c366, some c316, some c2546, some c102, some c82, some c70, some c313, some c1387, some c377, some c37, some c62, some c2372, some c311, some c284, some c341, some c8, some c2521, some c5, some c1118, some c2547, some c162, some c2044, some c2549, some c841, some c1033, some c2421, some c128, some c181, some c280, some c1862, some c2548, some c224, some c111, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]]
theorem checked2550 : lratChecker f2550 p2550 = .success := by decide +kernel
theorem unsat2550 : Unsatisfiable (PosFin 57) f2550 := by
  apply lratCheckerSound f2550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2550
  · intro a ha; simp [p2550] at ha; subst a; trivial
  · exact checked2550
theorem derived2550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2550 := by
  apply localUnsat_implies_entails f2550 [c2455, c2529, c2544, c2201, c2545, c2059, c2025, c2037, c2035, c367, c366, c316, c2546, c102, c82, c70, c313, c1387, c377, c37, c62, c2372, c311, c284, c341, c8, c2521, c5, c1118, c2547, c162, c2044, c2549, c841, c1033, c2421, c128, c181, c280, c1862, c2548, c224, c111] c2550 unsat2550 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2545 := derived2545 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2025 := derived2025 a h
  have h7 : Entails.eval a c2037 := derived2037 a h
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c2546 := derived2546 a h
  have h13 : Entails.eval a c102 := h 101 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c1387 := derived1387 a h
  have h18 : Entails.eval a c377 := h 376 (by decide)
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c62 := h 61 (by decide)
  have h21 : Entails.eval a c2372 := derived2372 a h
  have h22 : Entails.eval a c311 := h 310 (by decide)
  have h23 : Entails.eval a c284 := h 283 (by decide)
  have h24 : Entails.eval a c341 := h 340 (by decide)
  have h25 : Entails.eval a c8 := h 7 (by decide)
  have h26 : Entails.eval a c2521 := derived2521 a h
  have h27 : Entails.eval a c5 := h 4 (by decide)
  have h28 : Entails.eval a c1118 := derived1118 a h
  have h29 : Entails.eval a c2547 := derived2547 a h
  have h30 : Entails.eval a c162 := h 161 (by decide)
  have h31 : Entails.eval a c2044 := derived2044 a h
  have h32 : Entails.eval a c2549 := derived2549 a h
  have h33 : Entails.eval a c841 := derived841 a h
  have h34 : Entails.eval a c1033 := derived1033 a h
  have h35 : Entails.eval a c2421 := derived2421 a h
  have h36 : Entails.eval a c128 := h 127 (by decide)
  have h37 : Entails.eval a c181 := h 180 (by decide)
  have h38 : Entails.eval a c280 := h 279 (by decide)
  have h39 : Entails.eval a c1862 := derived1862 a h
  have h40 : Entails.eval a c2548 := derived2548 a h
  have h41 : Entails.eval a c224 := h 223 (by decide)
  have h42 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2551 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨48, by decide⟩, true), (⟨28, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c83, some c81, some c313, some c284, some c37, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2551 : lratChecker f2551 p2551 = .success := by decide +kernel
theorem unsat2551 : Unsatisfiable (PosFin 57) f2551 := by
  apply lratCheckerSound f2551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2551
  · intro a ha; simp [p2551] at ha; subst a; trivial
  · exact checked2551
theorem derived2551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2551 := by
  apply localUnsat_implies_entails f2551 [c2455, c2529, c83, c81, c313, c284, c37] c2551 unsat2551 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2552 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2545, some c2035, some c2025, some c2059, some c2550, some c2551, some c102, some c2037, some c69, some c94, some c365, some c313, some c377, some c37, some c62, some c284, some c314, some c2372, some c8, some c5, some c156, some c165, some c163, some c185, some c128, some c1033, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2552 : lratChecker f2552 p2552 = .success := by decide +kernel
theorem unsat2552 : Unsatisfiable (PosFin 57) f2552 := by
  apply lratCheckerSound f2552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2552
  · intro a ha; simp [p2552] at ha; subst a; trivial
  · exact checked2552
theorem derived2552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2552 := by
  apply localUnsat_implies_entails f2552 [c2455, c2529, c2544, c2545, c2035, c2025, c2059, c2550, c2551, c102, c2037, c69, c94, c365, c313, c377, c37, c62, c284, c314, c2372, c8, c5, c156, c165, c163, c185, c128, c1033] c2552 unsat2552 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2545 := derived2545 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2025 := derived2025 a h
  have h6 : Entails.eval a c2059 := derived2059 a h
  have h7 : Entails.eval a c2550 := derived2550 a h
  have h8 : Entails.eval a c2551 := derived2551 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c2037 := derived2037 a h
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c365 := h 364 (by decide)
  have h14 : Entails.eval a c313 := h 312 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c62 := h 61 (by decide)
  have h18 : Entails.eval a c284 := h 283 (by decide)
  have h19 : Entails.eval a c314 := h 313 (by decide)
  have h20 : Entails.eval a c2372 := derived2372 a h
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c5 := h 4 (by decide)
  have h23 : Entails.eval a c156 := h 155 (by decide)
  have h24 : Entails.eval a c165 := h 164 (by decide)
  have h25 : Entails.eval a c163 := h 162 (by decide)
  have h26 : Entails.eval a c185 := h 184 (by decide)
  have h27 : Entails.eval a c128 := h 127 (by decide)
  have h28 : Entails.eval a c1033 := derived1033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2553 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨44, by decide⟩, true), (⟨39, by decide⟩, true), (⟨46, by decide⟩, false), (⟨30, by decide⟩, false), (⟨53, by decide⟩, false), (⟨28, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c1396, some c379, some c1118, some c1491, some c155, some c161, some c164, some c559, some c129, some c108, some c114, some c227, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2553 : lratChecker f2553 p2553 = .success := by decide +kernel
theorem unsat2553 : Unsatisfiable (PosFin 57) f2553 := by
  apply lratCheckerSound f2553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2553
  · intro a ha; simp [p2553] at ha; subst a; trivial
  · exact checked2553
theorem derived2553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2553 := by
  apply localUnsat_implies_entails f2553 [c2529, c1396, c379, c1118, c1491, c155, c161, c164, c559, c129, c108, c114, c227] c2553 unsat2553 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c1396 := derived1396 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c1491 := derived1491 a h
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c559 := derived559 a h
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2554 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2037, some c2552, some c379, some c2550, some c1205, some c170, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2554 : lratChecker f2554 p2554 = .success := by decide +kernel
theorem unsat2554 : Unsatisfiable (PosFin 57) f2554 := by
  apply lratCheckerSound f2554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2554
  · intro a ha; simp [p2554] at ha; subst a; trivial
  · exact checked2554
theorem derived2554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2554 := by
  apply localUnsat_implies_entails f2554 [c2455, c2037, c2552, c379, c2550, c1205, c170] c2554 unsat2554 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2037 := derived2037 a h
  have h2 : Entails.eval a c2552 := derived2552 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c2550 := derived2550 a h
  have h5 : Entails.eval a c1205 := derived1205 a h
  have h6 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2555 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨12, by decide⟩, true), (⟨56, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2544, some c2201, some c2529, some c2455, some c2037, some c2059, some c2552, some c2545, some c2035, some c2025, some c2550, some c2551, some c102, some c300, some c50, some c1387, some c70, some c37, some c345, some c2490, some c1051, some c156, some c8, some c2553, some c2554, some c948, some c131, some c182, some c207, some c169, some c248, some c1223, some c107, some c223, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked2555 : lratChecker f2555 p2555 = .success := by decide +kernel
theorem unsat2555 : Unsatisfiable (PosFin 57) f2555 := by
  apply lratCheckerSound f2555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2555
  · intro a ha; simp [p2555] at ha; subst a; trivial
  · exact checked2555
theorem derived2555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2555 := by
  apply localUnsat_implies_entails f2555 [c2544, c2201, c2529, c2455, c2037, c2059, c2552, c2545, c2035, c2025, c2550, c2551, c102, c300, c50, c1387, c70, c37, c345, c2490, c1051, c156, c8, c2553, c2554, c948, c131, c182, c207, c169, c248, c1223, c107, c223] c2555 unsat2555 (by rfl) a
  have h0 : Entails.eval a c2544 := derived2544 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2455 := derived2455 a h
  have h4 : Entails.eval a c2037 := derived2037 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2552 := derived2552 a h
  have h7 : Entails.eval a c2545 := derived2545 a h
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c2025 := derived2025 a h
  have h10 : Entails.eval a c2550 := derived2550 a h
  have h11 : Entails.eval a c2551 := derived2551 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c300 := h 299 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c1387 := derived1387 a h
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c345 := h 344 (by decide)
  have h19 : Entails.eval a c2490 := derived2490 a h
  have h20 : Entails.eval a c1051 := derived1051 a h
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c8 := h 7 (by decide)
  have h23 : Entails.eval a c2553 := derived2553 a h
  have h24 : Entails.eval a c2554 := derived2554 a h
  have h25 : Entails.eval a c948 := derived948 a h
  have h26 : Entails.eval a c131 := h 130 (by decide)
  have h27 : Entails.eval a c182 := h 181 (by decide)
  have h28 : Entails.eval a c207 := h 206 (by decide)
  have h29 : Entails.eval a c169 := h 168 (by decide)
  have h30 : Entails.eval a c248 := h 247 (by decide)
  have h31 : Entails.eval a c1223 := derived1223 a h
  have h32 : Entails.eval a c107 := h 106 (by decide)
  have h33 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2556 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2059, some c2037, some c2552, some c300, some c2545, some c2035, some c2025, some c2550, some c2551, some c102, some c50, some c309, some c200, some c1387, some c70, some c37, some c150, some c169, some c227, some c133, some c114, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2556 : lratChecker f2556 p2556 = .success := by decide +kernel
theorem unsat2556 : Unsatisfiable (PosFin 57) f2556 := by
  apply lratCheckerSound f2556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2556
  · intro a ha; simp [p2556] at ha; subst a; trivial
  · exact checked2556
theorem derived2556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2556 := by
  apply localUnsat_implies_entails f2556 [c2529, c2455, c2059, c2037, c2552, c300, c2545, c2035, c2025, c2550, c2551, c102, c50, c309, c200, c1387, c70, c37, c150, c169, c227, c133, c114] c2556 unsat2556 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2059 := derived2059 a h
  have h3 : Entails.eval a c2037 := derived2037 a h
  have h4 : Entails.eval a c2552 := derived2552 a h
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c2545 := derived2545 a h
  have h7 : Entails.eval a c2035 := derived2035 a h
  have h8 : Entails.eval a c2025 := derived2025 a h
  have h9 : Entails.eval a c2550 := derived2550 a h
  have h10 : Entails.eval a c2551 := derived2551 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c1387 := derived1387 a h
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c150 := h 149 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c227 := h 226 (by decide)
  have h21 : Entails.eval a c133 := h 132 (by decide)
  have h22 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2557 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨56, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2544, some c2201, some c2529, some c2455, some c2037, some c2059, some c2552, some c2545, some c2035, some c2025, some c2550, some c2551, some c102, some c300, some c50, some c1387, some c70, some c37, some c345, some c2490, some c1051, some c156, some c8, some c2553, some c2554, some c948, some c309, some c1396, some c2555, some c180, some c559, some c200, some c2556, some c242, some c1223, some c217, some c223, some c136, some c107, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]]
theorem checked2557 : lratChecker f2557 p2557 = .success := by decide +kernel
theorem unsat2557 : Unsatisfiable (PosFin 57) f2557 := by
  apply lratCheckerSound f2557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2557
  · intro a ha; simp [p2557] at ha; subst a; trivial
  · exact checked2557
theorem derived2557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2557 := by
  apply localUnsat_implies_entails f2557 [c2544, c2201, c2529, c2455, c2037, c2059, c2552, c2545, c2035, c2025, c2550, c2551, c102, c300, c50, c1387, c70, c37, c345, c2490, c1051, c156, c8, c2553, c2554, c948, c309, c1396, c2555, c180, c559, c200, c2556, c242, c1223, c217, c223, c136, c107] c2557 unsat2557 (by rfl) a
  have h0 : Entails.eval a c2544 := derived2544 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2455 := derived2455 a h
  have h4 : Entails.eval a c2037 := derived2037 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2552 := derived2552 a h
  have h7 : Entails.eval a c2545 := derived2545 a h
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c2025 := derived2025 a h
  have h10 : Entails.eval a c2550 := derived2550 a h
  have h11 : Entails.eval a c2551 := derived2551 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c300 := h 299 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c1387 := derived1387 a h
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c345 := h 344 (by decide)
  have h19 : Entails.eval a c2490 := derived2490 a h
  have h20 : Entails.eval a c1051 := derived1051 a h
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c8 := h 7 (by decide)
  have h23 : Entails.eval a c2553 := derived2553 a h
  have h24 : Entails.eval a c2554 := derived2554 a h
  have h25 : Entails.eval a c948 := derived948 a h
  have h26 : Entails.eval a c309 := h 308 (by decide)
  have h27 : Entails.eval a c1396 := derived1396 a h
  have h28 : Entails.eval a c2555 := derived2555 a h
  have h29 : Entails.eval a c180 := h 179 (by decide)
  have h30 : Entails.eval a c559 := derived559 a h
  have h31 : Entails.eval a c200 := h 199 (by decide)
  have h32 : Entails.eval a c2556 := derived2556 a h
  have h33 : Entails.eval a c242 := h 241 (by decide)
  have h34 : Entails.eval a c1223 := derived1223 a h
  have h35 : Entails.eval a c217 := h 216 (by decide)
  have h36 : Entails.eval a c223 := h 222 (by decide)
  have h37 : Entails.eval a c136 := h 135 (by decide)
  have h38 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2558 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2201, some c2554, some c2025, some c2059, some c2037, some c2552, some c300, some c37, some c345, some c2035, some c313, some c2545, some c2550, some c2551, some c102, some c50, some c309, some c1387, some c70, some c1396, some c156, some c1051, some c8, some c2557, some c187, some c129, some c160, some c180, some c559, some c200, some c114, some c227, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked2558 : lratChecker f2558 p2558 = .success := by decide +kernel
theorem unsat2558 : Unsatisfiable (PosFin 57) f2558 := by
  apply lratCheckerSound f2558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2558
  · intro a ha; simp [p2558] at ha; subst a; trivial
  · exact checked2558
theorem derived2558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2558 := by
  apply localUnsat_implies_entails f2558 [c2455, c2529, c2201, c2554, c2025, c2059, c2037, c2552, c300, c37, c345, c2035, c313, c2545, c2550, c2551, c102, c50, c309, c1387, c70, c1396, c156, c1051, c8, c2557, c187, c129, c160, c180, c559, c200, c114, c227] c2558 unsat2558 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2554 := derived2554 a h
  have h4 : Entails.eval a c2025 := derived2025 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2037 := derived2037 a h
  have h7 : Entails.eval a c2552 := derived2552 a h
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c2035 := derived2035 a h
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c2545 := derived2545 a h
  have h14 : Entails.eval a c2550 := derived2550 a h
  have h15 : Entails.eval a c2551 := derived2551 a h
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  have h19 : Entails.eval a c1387 := derived1387 a h
  have h20 : Entails.eval a c70 := h 69 (by decide)
  have h21 : Entails.eval a c1396 := derived1396 a h
  have h22 : Entails.eval a c156 := h 155 (by decide)
  have h23 : Entails.eval a c1051 := derived1051 a h
  have h24 : Entails.eval a c8 := h 7 (by decide)
  have h25 : Entails.eval a c2557 := derived2557 a h
  have h26 : Entails.eval a c187 := h 186 (by decide)
  have h27 : Entails.eval a c129 := h 128 (by decide)
  have h28 : Entails.eval a c160 := h 159 (by decide)
  have h29 : Entails.eval a c180 := h 179 (by decide)
  have h30 : Entails.eval a c559 := derived559 a h
  have h31 : Entails.eval a c200 := h 199 (by decide)
  have h32 : Entails.eval a c114 := h 113 (by decide)
  have h33 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2559 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2201, some c2037, some c2035, some c2025, some c2059, some c2545, some c2550, some c2551, some c102, some c2552, some c300, some c1387, some c50, some c37, some c70, some c309, some c345, some c2490, some c2554, some c2558, some c5, some c11, some c841, some c2553, some c180, some c173, some c129, some c1223, some c165, some c223, some c182, some c197, some c107, some c242, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked2559 : lratChecker f2559 p2559 = .success := by decide +kernel
theorem unsat2559 : Unsatisfiable (PosFin 57) f2559 := by
  apply lratCheckerSound f2559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2559
  · intro a ha; simp [p2559] at ha; subst a; trivial
  · exact checked2559
theorem derived2559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2559 := by
  apply localUnsat_implies_entails f2559 [c2455, c2529, c2544, c2201, c2037, c2035, c2025, c2059, c2545, c2550, c2551, c102, c2552, c300, c1387, c50, c37, c70, c309, c345, c2490, c2554, c2558, c5, c11, c841, c2553, c180, c173, c129, c1223, c165, c223, c182, c197, c107, c242] c2559 unsat2559 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2037 := derived2037 a h
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2025 := derived2025 a h
  have h7 : Entails.eval a c2059 := derived2059 a h
  have h8 : Entails.eval a c2545 := derived2545 a h
  have h9 : Entails.eval a c2550 := derived2550 a h
  have h10 : Entails.eval a c2551 := derived2551 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c2552 := derived2552 a h
  have h13 : Entails.eval a c300 := h 299 (by decide)
  have h14 : Entails.eval a c1387 := derived1387 a h
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c2490 := derived2490 a h
  have h21 : Entails.eval a c2554 := derived2554 a h
  have h22 : Entails.eval a c2558 := derived2558 a h
  have h23 : Entails.eval a c5 := h 4 (by decide)
  have h24 : Entails.eval a c11 := h 10 (by decide)
  have h25 : Entails.eval a c841 := derived841 a h
  have h26 : Entails.eval a c2553 := derived2553 a h
  have h27 : Entails.eval a c180 := h 179 (by decide)
  have h28 : Entails.eval a c173 := h 172 (by decide)
  have h29 : Entails.eval a c129 := h 128 (by decide)
  have h30 : Entails.eval a c1223 := derived1223 a h
  have h31 : Entails.eval a c165 := h 164 (by decide)
  have h32 : Entails.eval a c223 := h 222 (by decide)
  have h33 : Entails.eval a c182 := h 181 (by decide)
  have h34 : Entails.eval a c197 := h 196 (by decide)
  have h35 : Entails.eval a c107 := h 106 (by decide)
  have h36 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2560 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c107, some c245, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2560 : lratChecker f2560 p2560 = .success := by decide +kernel
theorem unsat2560 : Unsatisfiable (PosFin 57) f2560 := by
  apply lratCheckerSound f2560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2560
  · intro a ha; simp [p2560] at ha; subst a; trivial
  · exact checked2560
theorem derived2560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2560 := by
  apply localUnsat_implies_entails f2560 [c106, c107, c245] c2560 unsat2560 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2561 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨45, by decide⟩, false), (⟨32, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c224, some c221, some c207, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2561 : lratChecker f2561 p2561 = .success := by decide +kernel
theorem unsat2561 : Unsatisfiable (PosFin 57) f2561 := by
  apply lratCheckerSound f2561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2561
  · intro a ha; simp [p2561] at ha; subst a; trivial
  · exact checked2561
theorem derived2561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2561 := by
  apply localUnsat_implies_entails f2561 [c224, c221, c207] c2561 unsat2561 (by rfl) a
  have h0 : Entails.eval a c224 := h 223 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2562 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2201, some c2544, some c2035, some c2559, some c276, some c366, some c367, some c2037, some c69, some c2019, some c273, some c2532, some c37, some c2038, some c2033, some c102, some c324, some c70, some c50, some c377, some c301, some c2372, some c2521, some c5, some c1031, some c1118, some c2561, some c209, some c2053, some c138, some c27, some c245, some c2560, some c204, some c119, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked2562 : lratChecker f2562 p2562 = .success := by decide +kernel
theorem unsat2562 : Unsatisfiable (PosFin 57) f2562 := by
  apply lratCheckerSound f2562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2562
  · intro a ha; simp [p2562] at ha; subst a; trivial
  · exact checked2562
theorem derived2562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2562 := by
  apply localUnsat_implies_entails f2562 [c2455, c2529, c2201, c2544, c2035, c2559, c276, c366, c367, c2037, c69, c2019, c273, c2532, c37, c2038, c2033, c102, c324, c70, c50, c377, c301, c2372, c2521, c5, c1031, c1118, c2561, c209, c2053, c138, c27, c245, c2560, c204, c119] c2562 unsat2562 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2559 := derived2559 a h
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c2037 := derived2037 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c2019 := derived2019 a h
  have h12 : Entails.eval a c273 := h 272 (by decide)
  have h13 : Entails.eval a c2532 := derived2532 a h
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c2038 := derived2038 a h
  have h16 : Entails.eval a c2033 := derived2033 a h
  have h17 : Entails.eval a c102 := h 101 (by decide)
  have h18 : Entails.eval a c324 := h 323 (by decide)
  have h19 : Entails.eval a c70 := h 69 (by decide)
  have h20 : Entails.eval a c50 := h 49 (by decide)
  have h21 : Entails.eval a c377 := h 376 (by decide)
  have h22 : Entails.eval a c301 := h 300 (by decide)
  have h23 : Entails.eval a c2372 := derived2372 a h
  have h24 : Entails.eval a c2521 := derived2521 a h
  have h25 : Entails.eval a c5 := h 4 (by decide)
  have h26 : Entails.eval a c1031 := derived1031 a h
  have h27 : Entails.eval a c1118 := derived1118 a h
  have h28 : Entails.eval a c2561 := derived2561 a h
  have h29 : Entails.eval a c209 := h 208 (by decide)
  have h30 : Entails.eval a c2053 := derived2053 a h
  have h31 : Entails.eval a c138 := h 137 (by decide)
  have h32 : Entails.eval a c27 := h 26 (by decide)
  have h33 : Entails.eval a c245 := h 244 (by decide)
  have h34 : Entails.eval a c2560 := derived2560 a h
  have h35 : Entails.eval a c204 := h 203 (by decide)
  have h36 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2563 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2544, some c2455, some c2529, some c2201, some c2035, some c367, some c2037, some c2562, some c379, some c1118, some c11, some c2559, some c276, some c1404, some c366, some c2066, some c2038, some c377, some c2532, some c316, some c358, some c76, some c196, some c976, some c32, some c228, some c2521, some c109, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2563 : lratChecker f2563 p2563 = .success := by decide +kernel
theorem unsat2563 : Unsatisfiable (PosFin 57) f2563 := by
  apply lratCheckerSound f2563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2563
  · intro a ha; simp [p2563] at ha; subst a; trivial
  · exact checked2563
theorem derived2563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2563 := by
  apply localUnsat_implies_entails f2563 [c2544, c2455, c2529, c2201, c2035, c367, c2037, c2562, c379, c1118, c11, c2559, c276, c1404, c366, c2066, c2038, c377, c2532, c316, c358, c76, c196, c976, c32, c228, c2521, c109] c2563 unsat2563 (by rfl) a
  have h0 : Entails.eval a c2544 := derived2544 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c2037 := derived2037 a h
  have h7 : Entails.eval a c2562 := derived2562 a h
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c1118 := derived1118 a h
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c2559 := derived2559 a h
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c1404 := derived1404 a h
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c2066 := derived2066 a h
  have h16 : Entails.eval a c2038 := derived2038 a h
  have h17 : Entails.eval a c377 := h 376 (by decide)
  have h18 : Entails.eval a c2532 := derived2532 a h
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c358 := h 357 (by decide)
  have h21 : Entails.eval a c76 := h 75 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  have h23 : Entails.eval a c976 := derived976 a h
  have h24 : Entails.eval a c32 := h 31 (by decide)
  have h25 : Entails.eval a c228 := h 227 (by decide)
  have h26 : Entails.eval a c2521 := derived2521 a h
  have h27 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2564 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2559, some c2037, some c2035, some c366, some c276, some c2562, some c1404, some c2563, some c102, some c70, some c1387, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2564 : lratChecker f2564 p2564 = .success := by decide +kernel
theorem unsat2564 : Unsatisfiable (PosFin 57) f2564 := by
  apply lratCheckerSound f2564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2564
  · intro a ha; simp [p2564] at ha; subst a; trivial
  · exact checked2564
theorem derived2564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2564 := by
  apply localUnsat_implies_entails f2564 [c2529, c2455, c2559, c2037, c2035, c366, c276, c2562, c1404, c2563, c102, c70, c1387] c2564 unsat2564 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2559 := derived2559 a h
  have h3 : Entails.eval a c2037 := derived2037 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c2562 := derived2562 a h
  have h8 : Entails.eval a c1404 := derived1404 a h
  have h9 : Entails.eval a c2563 := derived2563 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c1387 := derived1387 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2565 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2564, some c2559, some c2037, some c2035, some c69, some c365, some c273, some c37, some c313, some c2038, some c2033, some c324, some c81, some c102, some c94, some c50, some c377, some c274, some c2372, some c8, some c5, some c156, some c165, some c163, some c185, some c144, some c1033, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2565 : lratChecker f2565 p2565 = .success := by decide +kernel
theorem unsat2565 : Unsatisfiable (PosFin 57) f2565 := by
  apply lratCheckerSound f2565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2565
  · intro a ha; simp [p2565] at ha; subst a; trivial
  · exact checked2565
theorem derived2565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2565 := by
  apply localUnsat_implies_entails f2565 [c2455, c2529, c2544, c2564, c2559, c2037, c2035, c69, c365, c273, c37, c313, c2038, c2033, c324, c81, c102, c94, c50, c377, c274, c2372, c8, c5, c156, c165, c163, c185, c144, c1033] c2565 unsat2565 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2564 := derived2564 a h
  have h4 : Entails.eval a c2559 := derived2559 a h
  have h5 : Entails.eval a c2037 := derived2037 a h
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c2038 := derived2038 a h
  have h13 : Entails.eval a c2033 := derived2033 a h
  have h14 : Entails.eval a c324 := h 323 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c50 := h 49 (by decide)
  have h19 : Entails.eval a c377 := h 376 (by decide)
  have h20 : Entails.eval a c274 := h 273 (by decide)
  have h21 : Entails.eval a c2372 := derived2372 a h
  have h22 : Entails.eval a c8 := h 7 (by decide)
  have h23 : Entails.eval a c5 := h 4 (by decide)
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c165 := h 164 (by decide)
  have h26 : Entails.eval a c163 := h 162 (by decide)
  have h27 : Entails.eval a c185 := h 184 (by decide)
  have h28 : Entails.eval a c144 := h 143 (by decide)
  have h29 : Entails.eval a c1033 := derived1033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2566 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2038, some c2066, some c2564, some c2035, some c72, some c83, some c81, some c1414, some c980, some c2486, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2566 : lratChecker f2566 p2566 = .success := by decide +kernel
theorem unsat2566 : Unsatisfiable (PosFin 57) f2566 := by
  apply lratCheckerSound f2566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2566
  · intro a ha; simp [p2566] at ha; subst a; trivial
  · exact checked2566
theorem derived2566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2566 := by
  apply localUnsat_implies_entails f2566 [c2455, c2529, c2038, c2066, c2564, c2035, c72, c83, c81, c1414, c980, c2486] c2566 unsat2566 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2038 := derived2038 a h
  have h3 : Entails.eval a c2066 := derived2066 a h
  have h4 : Entails.eval a c2564 := derived2564 a h
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c1414 := derived1414 a h
  have h10 : Entails.eval a c980 := derived980 a h
  have h11 : Entails.eval a c2486 := derived2486 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2567 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2566, some c2037, some c2066, some c377, some c2565, some c379, some c2564, some c70, some c358, some c154, some c1241, some c15, some c976, some c980, some c165, some c1240, some c372, some c187, some c167, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2567 : lratChecker f2567 p2567 = .success := by decide +kernel
theorem unsat2567 : Unsatisfiable (PosFin 57) f2567 := by
  apply lratCheckerSound f2567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2567
  · intro a ha; simp [p2567] at ha; subst a; trivial
  · exact checked2567
theorem derived2567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2567 := by
  apply localUnsat_implies_entails f2567 [c2455, c2529, c2566, c2037, c2066, c377, c2565, c379, c2564, c70, c358, c154, c1241, c15, c976, c980, c165, c1240, c372, c187, c167] c2567 unsat2567 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2566 := derived2566 a h
  have h3 : Entails.eval a c2037 := derived2037 a h
  have h4 : Entails.eval a c2066 := derived2066 a h
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c2565 := derived2565 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c2564 := derived2564 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c1241 := derived1241 a h
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c976 := derived976 a h
  have h15 : Entails.eval a c980 := derived980 a h
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c1240 := derived1240 a h
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c187 := h 186 (by decide)
  have h20 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2568 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2035, some c2038, some c2567, some c314, some c2559, some c274, some c2066, some c2565, some c2037, some c300, some c305, some c36, some c272, some c334, some c2135, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2568 : lratChecker f2568 p2568 = .success := by decide +kernel
theorem unsat2568 : Unsatisfiable (PosFin 57) f2568 := by
  apply lratCheckerSound f2568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2568
  · intro a ha; simp [p2568] at ha; subst a; trivial
  · exact checked2568
theorem derived2568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2568 := by
  apply localUnsat_implies_entails f2568 [c2455, c2529, c2035, c2038, c2567, c314, c2559, c274, c2066, c2565, c2037, c300, c305, c36, c272, c334, c2135] c2568 unsat2568 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c2038 := derived2038 a h
  have h4 : Entails.eval a c2567 := derived2567 a h
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c2559 := derived2559 a h
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c2066 := derived2066 a h
  have h9 : Entails.eval a c2565 := derived2565 a h
  have h10 : Entails.eval a c2037 := derived2037 a h
  have h11 : Entails.eval a c300 := h 299 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c334 := h 333 (by decide)
  have h16 : Entails.eval a c2135 := derived2135 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2569 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2565, some c2037, some c2066, some c2568, some c37, some c44, some c340, some c294, some c36, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2569 : lratChecker f2569 p2569 = .success := by decide +kernel
theorem unsat2569 : Unsatisfiable (PosFin 57) f2569 := by
  apply lratCheckerSound f2569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2569
  · intro a ha; simp [p2569] at ha; subst a; trivial
  · exact checked2569
theorem derived2569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2569 := by
  apply localUnsat_implies_entails f2569 [c2529, c2455, c2565, c2037, c2066, c2568, c37, c44, c340, c294, c36] c2569 unsat2569 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2565 := derived2565 a h
  have h3 : Entails.eval a c2037 := derived2037 a h
  have h4 : Entails.eval a c2066 := derived2066 a h
  have h5 : Entails.eval a c2568 := derived2568 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c340 := h 339 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2570 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2201, some c2037, some c2565, some c379, some c2564, some c2035, some c72, some c1414, some c841, some c1118, some c155, some c11, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2570 : lratChecker f2570 p2570 = .success := by decide +kernel
theorem unsat2570 : Unsatisfiable (PosFin 57) f2570 := by
  apply lratCheckerSound f2570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2570
  · intro a ha; simp [p2570] at ha; subst a; trivial
  · exact checked2570
theorem derived2570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2570 := by
  apply localUnsat_implies_entails f2570 [c2455, c2529, c2544, c2201, c2037, c2565, c379, c2564, c2035, c72, c1414, c841, c1118, c155, c11] c2570 unsat2570 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2037 := derived2037 a h
  have h5 : Entails.eval a c2565 := derived2565 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c2564 := derived2564 a h
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c1414 := derived1414 a h
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2571 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2201, some c2564, some c1051, some c2559, some c2035, some c2565, some c2037, some c2569, some c2570, some c102, some c1387, some c70, some c274, some c50, some c305, some c156, some c8, some c952, some c38, some c300, some c36, some c349, some c340, some c1142, some c169, some c182, some c120, some c117, some c205, some c248, some c212, some c114, some c227, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked2571 : lratChecker f2571 p2571 = .success := by decide +kernel
theorem unsat2571 : Unsatisfiable (PosFin 57) f2571 := by
  apply lratCheckerSound f2571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2571
  · intro a ha; simp [p2571] at ha; subst a; trivial
  · exact checked2571
theorem derived2571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2571 := by
  apply localUnsat_implies_entails f2571 [c2455, c2529, c2201, c2564, c1051, c2559, c2035, c2565, c2037, c2569, c2570, c102, c1387, c70, c274, c50, c305, c156, c8, c952, c38, c300, c36, c349, c340, c1142, c169, c182, c120, c117, c205, c248, c212, c114, c227] c2571 unsat2571 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2564 := derived2564 a h
  have h4 : Entails.eval a c1051 := derived1051 a h
  have h5 : Entails.eval a c2559 := derived2559 a h
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c2565 := derived2565 a h
  have h8 : Entails.eval a c2037 := derived2037 a h
  have h9 : Entails.eval a c2569 := derived2569 a h
  have h10 : Entails.eval a c2570 := derived2570 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c1387 := derived1387 a h
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c274 := h 273 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c305 := h 304 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c952 := derived952 a h
  have h20 : Entails.eval a c38 := h 37 (by decide)
  have h21 : Entails.eval a c300 := h 299 (by decide)
  have h22 : Entails.eval a c36 := h 35 (by decide)
  have h23 : Entails.eval a c349 := h 348 (by decide)
  have h24 : Entails.eval a c340 := h 339 (by decide)
  have h25 : Entails.eval a c1142 := derived1142 a h
  have h26 : Entails.eval a c169 := h 168 (by decide)
  have h27 : Entails.eval a c182 := h 181 (by decide)
  have h28 : Entails.eval a c120 := h 119 (by decide)
  have h29 : Entails.eval a c117 := h 116 (by decide)
  have h30 : Entails.eval a c205 := h 204 (by decide)
  have h31 : Entails.eval a c248 := h 247 (by decide)
  have h32 : Entails.eval a c212 := h 211 (by decide)
  have h33 : Entails.eval a c114 := h 113 (by decide)
  have h34 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2572 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2569, some c2570, some c102, some c2559, some c2035, some c2565, some c2037, some c1387, some c70, some c274, some c38, some c50, some c300, some c36, some c349, some c340, some c248, some c242, some c212, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2572 : lratChecker f2572 p2572 = .success := by decide +kernel
theorem unsat2572 : Unsatisfiable (PosFin 57) f2572 := by
  apply lratCheckerSound f2572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2572
  · intro a ha; simp [p2572] at ha; subst a; trivial
  · exact checked2572
theorem derived2572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2572 := by
  apply localUnsat_implies_entails f2572 [c2455, c2529, c2569, c2570, c102, c2559, c2035, c2565, c2037, c1387, c70, c274, c38, c50, c300, c36, c349, c340, c248, c242, c212] c2572 unsat2572 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2569 := derived2569 a h
  have h3 : Entails.eval a c2570 := derived2570 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c2559 := derived2559 a h
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c2565 := derived2565 a h
  have h8 : Entails.eval a c2037 := derived2037 a h
  have h9 : Entails.eval a c1387 := derived1387 a h
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c300 := h 299 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c340 := h 339 (by decide)
  have h18 : Entails.eval a c248 := h 247 (by decide)
  have h19 : Entails.eval a c242 := h 241 (by decide)
  have h20 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2573 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2544, some c2201, some c2565, some c2037, some c2569, some c2570, some c102, some c2559, some c2035, some c1387, some c70, some c274, some c50, some c300, some c305, some c2571, some c2572, some c204, some c27, some c379, some c2564, some c1237, some c1051, some c36, some c38, some c314, some c2490, some c1491, some c155, some c164, some c141, some c145, some c250, some c210, some c114, some c222, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked2573 : lratChecker f2573 p2573 = .success := by decide +kernel
theorem unsat2573 : Unsatisfiable (PosFin 57) f2573 := by
  apply lratCheckerSound f2573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2573
  · intro a ha; simp [p2573] at ha; subst a; trivial
  · exact checked2573
theorem derived2573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2573 := by
  apply localUnsat_implies_entails f2573 [c2529, c2455, c2544, c2201, c2565, c2037, c2569, c2570, c102, c2559, c2035, c1387, c70, c274, c50, c300, c305, c2571, c2572, c204, c27, c379, c2564, c1237, c1051, c36, c38, c314, c2490, c1491, c155, c164, c141, c145, c250, c210, c114, c222] c2573 unsat2573 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2565 := derived2565 a h
  have h5 : Entails.eval a c2037 := derived2037 a h
  have h6 : Entails.eval a c2569 := derived2569 a h
  have h7 : Entails.eval a c2570 := derived2570 a h
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c2559 := derived2559 a h
  have h10 : Entails.eval a c2035 := derived2035 a h
  have h11 : Entails.eval a c1387 := derived1387 a h
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c274 := h 273 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c305 := h 304 (by decide)
  have h17 : Entails.eval a c2571 := derived2571 a h
  have h18 : Entails.eval a c2572 := derived2572 a h
  have h19 : Entails.eval a c204 := h 203 (by decide)
  have h20 : Entails.eval a c27 := h 26 (by decide)
  have h21 : Entails.eval a c379 := h 378 (by decide)
  have h22 : Entails.eval a c2564 := derived2564 a h
  have h23 : Entails.eval a c1237 := derived1237 a h
  have h24 : Entails.eval a c1051 := derived1051 a h
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c38 := h 37 (by decide)
  have h27 : Entails.eval a c314 := h 313 (by decide)
  have h28 : Entails.eval a c2490 := derived2490 a h
  have h29 : Entails.eval a c1491 := derived1491 a h
  have h30 : Entails.eval a c155 := h 154 (by decide)
  have h31 : Entails.eval a c164 := h 163 (by decide)
  have h32 : Entails.eval a c141 := h 140 (by decide)
  have h33 : Entails.eval a c145 := h 144 (by decide)
  have h34 : Entails.eval a c250 := h 249 (by decide)
  have h35 : Entails.eval a c210 := h 209 (by decide)
  have h36 : Entails.eval a c114 := h 113 (by decide)
  have h37 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2574 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2201, some c2544, some c2565, some c2037, some c2569, some c2570, some c102, some c2559, some c2035, some c1387, some c70, some c274, some c50, some c300, some c36, some c38, some c314, some c305, some c379, some c2564, some c156, some c1051, some c8, some c952, some c2571, some c1237, some c2572, some c205, some c204, some c120, some c27, some c2573, some c223, some c210, some c107, some c141, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked2574 : lratChecker f2574 p2574 = .success := by decide +kernel
theorem unsat2574 : Unsatisfiable (PosFin 57) f2574 := by
  apply lratCheckerSound f2574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2574
  · intro a ha; simp [p2574] at ha; subst a; trivial
  · exact checked2574
theorem derived2574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2574 := by
  apply localUnsat_implies_entails f2574 [c2529, c2455, c2201, c2544, c2565, c2037, c2569, c2570, c102, c2559, c2035, c1387, c70, c274, c50, c300, c36, c38, c314, c305, c379, c2564, c156, c1051, c8, c952, c2571, c1237, c2572, c205, c204, c120, c27, c2573, c223, c210, c107, c141] c2574 unsat2574 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2565 := derived2565 a h
  have h5 : Entails.eval a c2037 := derived2037 a h
  have h6 : Entails.eval a c2569 := derived2569 a h
  have h7 : Entails.eval a c2570 := derived2570 a h
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c2559 := derived2559 a h
  have h10 : Entails.eval a c2035 := derived2035 a h
  have h11 : Entails.eval a c1387 := derived1387 a h
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c274 := h 273 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c38 := h 37 (by decide)
  have h18 : Entails.eval a c314 := h 313 (by decide)
  have h19 : Entails.eval a c305 := h 304 (by decide)
  have h20 : Entails.eval a c379 := h 378 (by decide)
  have h21 : Entails.eval a c2564 := derived2564 a h
  have h22 : Entails.eval a c156 := h 155 (by decide)
  have h23 : Entails.eval a c1051 := derived1051 a h
  have h24 : Entails.eval a c8 := h 7 (by decide)
  have h25 : Entails.eval a c952 := derived952 a h
  have h26 : Entails.eval a c2571 := derived2571 a h
  have h27 : Entails.eval a c1237 := derived1237 a h
  have h28 : Entails.eval a c2572 := derived2572 a h
  have h29 : Entails.eval a c205 := h 204 (by decide)
  have h30 : Entails.eval a c204 := h 203 (by decide)
  have h31 : Entails.eval a c120 := h 119 (by decide)
  have h32 : Entails.eval a c27 := h 26 (by decide)
  have h33 : Entails.eval a c2573 := derived2573 a h
  have h34 : Entails.eval a c223 := h 222 (by decide)
  have h35 : Entails.eval a c210 := h 209 (by decide)
  have h36 : Entails.eval a c107 := h 106 (by decide)
  have h37 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2575 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2544, some c2201, some c2574, some c841, some c2037, some c2565, some c379, some c1118, some c155, some c11, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2575 : lratChecker f2575 p2575 = .success := by decide +kernel
theorem unsat2575 : Unsatisfiable (PosFin 57) f2575 := by
  apply lratCheckerSound f2575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2575
  · intro a ha; simp [p2575] at ha; subst a; trivial
  · exact checked2575
theorem derived2575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2575 := by
  apply localUnsat_implies_entails f2575 [c2455, c2544, c2201, c2574, c841, c2037, c2565, c379, c1118, c155, c11] c2575 unsat2575 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2544 := derived2544 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2574 := derived2574 a h
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c2037 := derived2037 a h
  have h6 : Entails.eval a c2565 := derived2565 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c1118 := derived1118 a h
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2576 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2201, some c2544, some c2575, some c2574, some c841, some c2565, some c2037, some c2569, some c2570, some c102, some c1387, some c70, some c379, some c1504, some c11, some c5, some c173, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2576 : lratChecker f2576 p2576 = .success := by decide +kernel
theorem unsat2576 : Unsatisfiable (PosFin 57) f2576 := by
  apply lratCheckerSound f2576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2576
  · intro a ha; simp [p2576] at ha; subst a; trivial
  · exact checked2576
theorem derived2576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2576 := by
  apply localUnsat_implies_entails f2576 [c2455, c2529, c2201, c2544, c2575, c2574, c841, c2565, c2037, c2569, c2570, c102, c1387, c70, c379, c1504, c11, c5, c173] c2576 unsat2576 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2575 := derived2575 a h
  have h5 : Entails.eval a c2574 := derived2574 a h
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c2565 := derived2565 a h
  have h8 : Entails.eval a c2037 := derived2037 a h
  have h9 : Entails.eval a c2569 := derived2569 a h
  have h10 : Entails.eval a c2570 := derived2570 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c1387 := derived1387 a h
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c379 := h 378 (by decide)
  have h15 : Entails.eval a c1504 := derived1504 a h
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c5 := h 4 (by decide)
  have h18 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2577 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2201, some c2544, some c2035, some c2037, some c2559, some c2564, some c2565, some c379, some c2569, some c2570, some c102, some c1387, some c70, some c2490, some c274, some c50, some c38, some c300, some c305, some c36, some c2574, some c841, some c2575, some c2576, some c1237, some c2572, some c11, some c948, some c205, some c204, some c180, some c223, some c145, some c165, some c107, some c120, some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p2577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked2577 : lratChecker f2577 p2577 = .success := by decide +kernel
theorem unsat2577 : Unsatisfiable (PosFin 57) f2577 := by
  apply lratCheckerSound f2577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2577
  · intro a ha; simp [p2577] at ha; subst a; trivial
  · exact checked2577
theorem derived2577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2577 := by
  apply localUnsat_implies_entails f2577 [c2529, c2455, c2201, c2544, c2035, c2037, c2559, c2564, c2565, c379, c2569, c2570, c102, c1387, c70, c2490, c274, c50, c38, c300, c305, c36, c2574, c841, c2575, c2576, c1237, c2572, c11, c948, c205, c204, c180, c223, c145, c165, c107, c120] c2577 unsat2577 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2037 := derived2037 a h
  have h6 : Entails.eval a c2559 := derived2559 a h
  have h7 : Entails.eval a c2564 := derived2564 a h
  have h8 : Entails.eval a c2565 := derived2565 a h
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c2569 := derived2569 a h
  have h11 : Entails.eval a c2570 := derived2570 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c1387 := derived1387 a h
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c2490 := derived2490 a h
  have h16 : Entails.eval a c274 := h 273 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c300 := h 299 (by decide)
  have h20 : Entails.eval a c305 := h 304 (by decide)
  have h21 : Entails.eval a c36 := h 35 (by decide)
  have h22 : Entails.eval a c2574 := derived2574 a h
  have h23 : Entails.eval a c841 := derived841 a h
  have h24 : Entails.eval a c2575 := derived2575 a h
  have h25 : Entails.eval a c2576 := derived2576 a h
  have h26 : Entails.eval a c1237 := derived1237 a h
  have h27 : Entails.eval a c2572 := derived2572 a h
  have h28 : Entails.eval a c11 := h 10 (by decide)
  have h29 : Entails.eval a c948 := derived948 a h
  have h30 : Entails.eval a c205 := h 204 (by decide)
  have h31 : Entails.eval a c204 := h 203 (by decide)
  have h32 : Entails.eval a c180 := h 179 (by decide)
  have h33 : Entails.eval a c223 := h 222 (by decide)
  have h34 : Entails.eval a c145 := h 144 (by decide)
  have h35 : Entails.eval a c165 := h 164 (by decide)
  have h36 : Entails.eval a c107 := h 106 (by decide)
  have h37 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2578 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2025, some c2059, some c2070, some c313, some c68, some c37, some c284, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2578 : lratChecker f2578 p2578 = .success := by decide +kernel
theorem unsat2578 : Unsatisfiable (PosFin 57) f2578 := by
  apply lratCheckerSound f2578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2578
  · intro a ha; simp [p2578] at ha; subst a; trivial
  · exact checked2578
theorem derived2578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2578 := by
  apply localUnsat_implies_entails f2578 [c2455, c2529, c2025, c2059, c2070, c313, c68, c37, c284] c2578 unsat2578 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2025 := derived2025 a h
  have h3 : Entails.eval a c2059 := derived2059 a h
  have h4 : Entails.eval a c2070 := derived2070 a h
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2579 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2529, some c2455, some c2248, some c2578, some c2541, some c37, some c313, some c880, some c2033, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2579 : lratChecker f2579 p2579 = .success := by decide +kernel
theorem unsat2579 : Unsatisfiable (PosFin 57) f2579 := by
  apply lratCheckerSound f2579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2579
  · intro a ha; simp [p2579] at ha; subst a; trivial
  · exact checked2579
theorem derived2579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2579 := by
  apply localUnsat_implies_entails f2579 [c2577, c2529, c2455, c2248, c2578, c2541, c37, c313, c880, c2033] c2579 unsat2579 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2455 := derived2455 a h
  have h3 : Entails.eval a c2248 := derived2248 a h
  have h4 : Entails.eval a c2578 := derived2578 a h
  have h5 : Entails.eval a c2541 := derived2541 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c880 := derived880 a h
  have h9 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2580 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2577, some c2579, some c2032, some c2068, some c2220, some c36, some c284, some c278, some c44, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2580 : lratChecker f2580 p2580 = .success := by decide +kernel
theorem unsat2580 : Unsatisfiable (PosFin 57) f2580 := by
  apply lratCheckerSound f2580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2580
  · intro a ha; simp [p2580] at ha; subst a; trivial
  · exact checked2580
theorem derived2580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2580 := by
  apply localUnsat_implies_entails f2580 [c2529, c2455, c2577, c2579, c2032, c2068, c2220, c36, c284, c278, c44] c2580 unsat2580 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2579 := derived2579 a h
  have h4 : Entails.eval a c2032 := derived2032 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c2220 := derived2220 a h
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2580

end CochromaticTwenty.Certificates.B16_8_2
