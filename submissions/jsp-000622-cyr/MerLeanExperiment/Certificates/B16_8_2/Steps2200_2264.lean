import MerLeanExperiment.Certificates.B16_8_2.Steps2100_2199

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2581 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c69, some c88, some c2580, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2581 : lratChecker f2581 p2581 = .success := by decide +kernel
theorem unsat2581 : Unsatisfiable (PosFin 57) f2581 := by
  apply lratCheckerSound f2581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2581
  · intro a ha; simp [p2581] at ha; subst a; trivial
  · exact checked2581
theorem derived2581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2581 := by
  apply localUnsat_implies_entails f2581 [c2529, c69, c88, c2580] c2581 unsat2581 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c2580 := derived2580 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2582 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨37, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2529, some c69, some c94, some c2043, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2582 : lratChecker f2582 p2582 = .success := by decide +kernel
theorem unsat2582 : Unsatisfiable (PosFin 57) f2582 := by
  apply lratCheckerSound f2582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2582
  · intro a ha; simp [p2582] at ha; subst a; trivial
  · exact checked2582
theorem derived2582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2582 := by
  apply localUnsat_implies_entails f2582 [c2577, c2529, c69, c94, c2043] c2582 unsat2582 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c2043 := derived2043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2583 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2581, some c69, some c2025, some c2059, some c313, some c37, some c284, some c2582, some c102, some c81, some c2040, some c316, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2583 : lratChecker f2583 p2583 = .success := by decide +kernel
theorem unsat2583 : Unsatisfiable (PosFin 57) f2583 := by
  apply lratCheckerSound f2583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2583
  · intro a ha; simp [p2583] at ha; subst a; trivial
  · exact checked2583
theorem derived2583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2583 := by
  apply localUnsat_implies_entails f2583 [c2455, c2529, c2581, c69, c2025, c2059, c313, c37, c284, c2582, c102, c81, c2040, c316] c2583 unsat2583 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2581 := derived2581 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c2025 := derived2025 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c2582 := derived2582 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c2040 := derived2040 a h
  have h13 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2584 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2577, some c2583, some c2541, some c94, some c50, some c290, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2584 : lratChecker f2584 p2584 = .success := by decide +kernel
theorem unsat2584 : Unsatisfiable (PosFin 57) f2584 := by
  apply lratCheckerSound f2584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2584
  · intro a ha; simp [p2584] at ha; subst a; trivial
  · exact checked2584
theorem derived2584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2584 := by
  apply localUnsat_implies_entails f2584 [c2529, c2577, c2583, c2541, c94, c50, c290] c2584 unsat2584 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c2583 := derived2583 a h
  have h3 : Entails.eval a c2541 := derived2541 a h
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2585 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2455, some c2529, some c2581, some c69, some c2583, some c2541, some c37, some c313, some c2033, some c324, some c2584, some c102, some c81, some c51, some c276, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2585 : lratChecker f2585 p2585 = .success := by decide +kernel
theorem unsat2585 : Unsatisfiable (PosFin 57) f2585 := by
  apply lratCheckerSound f2585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2585
  · intro a ha; simp [p2585] at ha; subst a; trivial
  · exact checked2585
theorem derived2585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2585 := by
  apply localUnsat_implies_entails f2585 [c2577, c2455, c2529, c2581, c69, c2583, c2541, c37, c313, c2033, c324, c2584, c102, c81, c51, c276] c2585 unsat2585 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2581 := derived2581 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c2583 := derived2583 a h
  have h6 : Entails.eval a c2541 := derived2541 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c2033 := derived2033 a h
  have h10 : Entails.eval a c324 := h 323 (by decide)
  have h11 : Entails.eval a c2584 := derived2584 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2586 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2577, some c2585, some c2032, some c69, some c2059, some c284, some c37, some c324, some c2025, some c95, some c61, some c332, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2586 : lratChecker f2586 p2586 = .success := by decide +kernel
theorem unsat2586 : Unsatisfiable (PosFin 57) f2586 := by
  apply lratCheckerSound f2586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2586
  · intro a ha; simp [p2586] at ha; subst a; trivial
  · exact checked2586
theorem derived2586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2586 := by
  apply localUnsat_implies_entails f2586 [c2529, c2455, c2577, c2585, c2032, c69, c2059, c284, c37, c324, c2025, c95, c61, c332] c2586 unsat2586 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2585 := derived2585 a h
  have h4 : Entails.eval a c2032 := derived2032 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c2059 := derived2059 a h
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c2025 := derived2025 a h
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2587 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2529, some c2455, some c2201, some c2544, some c2059, some c2585, some c2032, some c69, some c284, some c2581, some c2586, some c102, some c50, some c285, some c94, some c301, some c374, some c37, some c324, some c2025, some c345, some c371, some c129, some c177, some c182, some c2112, some c131, some c948, some c207, some c232, some c216, some c107, some c253, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked2587 : lratChecker f2587 p2587 = .success := by decide +kernel
theorem unsat2587 : Unsatisfiable (PosFin 57) f2587 := by
  apply lratCheckerSound f2587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2587
  · intro a ha; simp [p2587] at ha; subst a; trivial
  · exact checked2587
theorem derived2587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2587 := by
  apply localUnsat_implies_entails f2587 [c2577, c2529, c2455, c2201, c2544, c2059, c2585, c2032, c69, c284, c2581, c2586, c102, c50, c285, c94, c301, c374, c37, c324, c2025, c345, c371, c129, c177, c182, c2112, c131, c948, c207, c232, c216, c107, c253] c2587 unsat2587 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2455 := derived2455 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2544 := derived2544 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2585 := derived2585 a h
  have h7 : Entails.eval a c2032 := derived2032 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c2581 := derived2581 a h
  have h11 : Entails.eval a c2586 := derived2586 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c37 := h 36 (by decide)
  have h19 : Entails.eval a c324 := h 323 (by decide)
  have h20 : Entails.eval a c2025 := derived2025 a h
  have h21 : Entails.eval a c345 := h 344 (by decide)
  have h22 : Entails.eval a c371 := h 370 (by decide)
  have h23 : Entails.eval a c129 := h 128 (by decide)
  have h24 : Entails.eval a c177 := h 176 (by decide)
  have h25 : Entails.eval a c182 := h 181 (by decide)
  have h26 : Entails.eval a c2112 := derived2112 a h
  have h27 : Entails.eval a c131 := h 130 (by decide)
  have h28 : Entails.eval a c948 := derived948 a h
  have h29 : Entails.eval a c207 := h 206 (by decide)
  have h30 : Entails.eval a c232 := h 231 (by decide)
  have h31 : Entails.eval a c216 := h 215 (by decide)
  have h32 : Entails.eval a c107 := h 106 (by decide)
  have h33 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2588 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2544, some c2529, some c2455, some c2059, some c2585, some c2032, some c69, some c284, some c2581, some c2586, some c102, some c50, some c285, some c2587, some c371, some c162, some c11, some c168, some c37, some c324, some c2025, some c345, some c232, some c234, some c216, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2588 : lratChecker f2588 p2588 = .success := by decide +kernel
theorem unsat2588 : Unsatisfiable (PosFin 57) f2588 := by
  apply lratCheckerSound f2588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2588
  · intro a ha; simp [p2588] at ha; subst a; trivial
  · exact checked2588
theorem derived2588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2588 := by
  apply localUnsat_implies_entails f2588 [c2201, c2544, c2529, c2455, c2059, c2585, c2032, c69, c284, c2581, c2586, c102, c50, c285, c2587, c371, c162, c11, c168, c37, c324, c2025, c345, c232, c234, c216] c2588 unsat2588 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2544 := derived2544 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2455 := derived2455 a h
  have h4 : Entails.eval a c2059 := derived2059 a h
  have h5 : Entails.eval a c2585 := derived2585 a h
  have h6 : Entails.eval a c2032 := derived2032 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c2581 := derived2581 a h
  have h10 : Entails.eval a c2586 := derived2586 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c285 := h 284 (by decide)
  have h14 : Entails.eval a c2587 := derived2587 a h
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c162 := h 161 (by decide)
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c324 := h 323 (by decide)
  have h21 : Entails.eval a c2025 := derived2025 a h
  have h22 : Entails.eval a c345 := h 344 (by decide)
  have h23 : Entails.eval a c232 := h 231 (by decide)
  have h24 : Entails.eval a c234 := h 233 (by decide)
  have h25 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2589 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2201, some c2455, some c2529, some c2544, some c2581, some c69, some c2585, some c2032, some c2059, some c284, some c2586, some c102, some c50, some c309, some c2588, some c200, some c21, some c285, some c371, some c2587, some c162, some c948, some c207, some c2025, some c94, some c330, some c374, some c37, some c1863, some c214, some c142, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked2589 : lratChecker f2589 p2589 = .success := by decide +kernel
theorem unsat2589 : Unsatisfiable (PosFin 57) f2589 := by
  apply lratCheckerSound f2589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2589
  · intro a ha; simp [p2589] at ha; subst a; trivial
  · exact checked2589
theorem derived2589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2589 := by
  apply localUnsat_implies_entails f2589 [c2577, c2201, c2455, c2529, c2544, c2581, c69, c2585, c2032, c2059, c284, c2586, c102, c50, c309, c2588, c200, c21, c285, c371, c2587, c162, c948, c207, c2025, c94, c330, c374, c37, c1863, c214, c142] c2589 unsat2589 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2455 := derived2455 a h
  have h3 : Entails.eval a c2529 := derived2529 a h
  have h4 : Entails.eval a c2544 := derived2544 a h
  have h5 : Entails.eval a c2581 := derived2581 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c2585 := derived2585 a h
  have h8 : Entails.eval a c2032 := derived2032 a h
  have h9 : Entails.eval a c2059 := derived2059 a h
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c2586 := derived2586 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c309 := h 308 (by decide)
  have h15 : Entails.eval a c2588 := derived2588 a h
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  have h18 : Entails.eval a c285 := h 284 (by decide)
  have h19 : Entails.eval a c371 := h 370 (by decide)
  have h20 : Entails.eval a c2587 := derived2587 a h
  have h21 : Entails.eval a c162 := h 161 (by decide)
  have h22 : Entails.eval a c948 := derived948 a h
  have h23 : Entails.eval a c207 := h 206 (by decide)
  have h24 : Entails.eval a c2025 := derived2025 a h
  have h25 : Entails.eval a c94 := h 93 (by decide)
  have h26 : Entails.eval a c330 := h 329 (by decide)
  have h27 : Entails.eval a c374 := h 373 (by decide)
  have h28 : Entails.eval a c37 := h 36 (by decide)
  have h29 : Entails.eval a c1863 := derived1863 a h
  have h30 : Entails.eval a c214 := h 213 (by decide)
  have h31 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2590 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2544, some c2577, some c69, some c2585, some c2032, some c371, some c2581, some c2025, some c2059, some c284, some c37, some c2586, some c102, some c94, some c50, some c309, some c285, some c2587, some c162, some c5, some c2588, some c200, some c2589, some c243, some c238, some c257, some c172, some c133, some c187, some c107, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked2590 : lratChecker f2590 p2590 = .success := by decide +kernel
theorem unsat2590 : Unsatisfiable (PosFin 57) f2590 := by
  apply lratCheckerSound f2590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2590
  · intro a ha; simp [p2590] at ha; subst a; trivial
  · exact checked2590
theorem derived2590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2590 := by
  apply localUnsat_implies_entails f2590 [c2455, c2529, c2544, c2577, c69, c2585, c2032, c371, c2581, c2025, c2059, c284, c37, c2586, c102, c94, c50, c309, c285, c2587, c162, c5, c2588, c200, c2589, c243, c238, c257, c172, c133, c187, c107] c2590 unsat2590 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c2577 := derived2577 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c2585 := derived2585 a h
  have h6 : Entails.eval a c2032 := derived2032 a h
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c2581 := derived2581 a h
  have h9 : Entails.eval a c2025 := derived2025 a h
  have h10 : Entails.eval a c2059 := derived2059 a h
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c2586 := derived2586 a h
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c309 := h 308 (by decide)
  have h18 : Entails.eval a c285 := h 284 (by decide)
  have h19 : Entails.eval a c2587 := derived2587 a h
  have h20 : Entails.eval a c162 := h 161 (by decide)
  have h21 : Entails.eval a c5 := h 4 (by decide)
  have h22 : Entails.eval a c2588 := derived2588 a h
  have h23 : Entails.eval a c200 := h 199 (by decide)
  have h24 : Entails.eval a c2589 := derived2589 a h
  have h25 : Entails.eval a c243 := h 242 (by decide)
  have h26 : Entails.eval a c238 := h 237 (by decide)
  have h27 : Entails.eval a c257 := h 256 (by decide)
  have h28 : Entails.eval a c172 := h 171 (by decide)
  have h29 : Entails.eval a c133 := h 132 (by decide)
  have h30 : Entails.eval a c187 := h 186 (by decide)
  have h31 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2591 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2577, some c2590, some c95, some c49, some c292, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2591 : lratChecker f2591 p2591 = .success := by decide +kernel
theorem unsat2591 : Unsatisfiable (PosFin 57) f2591 := by
  apply lratCheckerSound f2591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2591
  · intro a ha; simp [p2591] at ha; subst a; trivial
  · exact checked2591
theorem derived2591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2591 := by
  apply localUnsat_implies_entails f2591 [c2529, c2455, c2577, c2590, c95, c49, c292] c2591 unsat2591 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2590 := derived2590 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2592 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2577, some c2581, some c69, some c2585, some c2032, some c284, some c2591, some c102, some c94, some c374, some c36, some c1463, some c2590, some c371, some c158, some c2112, some c117, some c179, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2592 : lratChecker f2592 p2592 = .success := by decide +kernel
theorem unsat2592 : Unsatisfiable (PosFin 57) f2592 := by
  apply lratCheckerSound f2592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2592
  · intro a ha; simp [p2592] at ha; subst a; trivial
  · exact checked2592
theorem derived2592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2592 := by
  apply localUnsat_implies_entails f2592 [c2455, c2529, c2577, c2581, c69, c2585, c2032, c284, c2591, c102, c94, c374, c36, c1463, c2590, c371, c158, c2112, c117, c179] c2592 unsat2592 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2581 := derived2581 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c2585 := derived2585 a h
  have h6 : Entails.eval a c2032 := derived2032 a h
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c2591 := derived2591 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c1463 := derived1463 a h
  have h14 : Entails.eval a c2590 := derived2590 a h
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c2112 := derived2112 a h
  have h18 : Entails.eval a c117 := h 116 (by decide)
  have h19 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2593 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2201, some c2544, some c2577, some c2581, some c2592, some c5, some c11, some c69, some c2585, some c2032, some c284, some c2591, some c102, some c94, some c2590, some c172, some c173, some c150, some c117, some c187, some c1047, some c107, some c105, some c226, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2593 : lratChecker f2593 p2593 = .success := by decide +kernel
theorem unsat2593 : Unsatisfiable (PosFin 57) f2593 := by
  apply lratCheckerSound f2593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2593
  · intro a ha; simp [p2593] at ha; subst a; trivial
  · exact checked2593
theorem derived2593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2593 := by
  apply localUnsat_implies_entails f2593 [c2455, c2529, c2201, c2544, c2577, c2581, c2592, c5, c11, c69, c2585, c2032, c284, c2591, c102, c94, c2590, c172, c173, c150, c117, c187, c1047, c107, c105, c226] c2593 unsat2593 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2577 := derived2577 a h
  have h5 : Entails.eval a c2581 := derived2581 a h
  have h6 : Entails.eval a c2592 := derived2592 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c2585 := derived2585 a h
  have h11 : Entails.eval a c2032 := derived2032 a h
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c2591 := derived2591 a h
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c2590 := derived2590 a h
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c150 := h 149 (by decide)
  have h20 : Entails.eval a c117 := h 116 (by decide)
  have h21 : Entails.eval a c187 := h 186 (by decide)
  have h22 : Entails.eval a c1047 := derived1047 a h
  have h23 : Entails.eval a c107 := h 106 (by decide)
  have h24 : Entails.eval a c105 := h 104 (by decide)
  have h25 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2594 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2455, some c2529, some c2544, some c2201, some c2581, some c69, some c2585, some c2032, some c284, some c2591, some c102, some c94, some c2592, some c5, some c11, some c2590, some c290, some c305, some c2593, some c953, some c27, some c948, some c36, some c324, some c62, some c349, some c374, some c196, some c205, some c203, some c232, some c126, some c212, some c179, some c243, some c147, some c114, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked2594 : lratChecker f2594 p2594 = .success := by decide +kernel
theorem unsat2594 : Unsatisfiable (PosFin 57) f2594 := by
  apply lratCheckerSound f2594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2594
  · intro a ha; simp [p2594] at ha; subst a; trivial
  · exact checked2594
theorem derived2594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2594 := by
  apply localUnsat_implies_entails f2594 [c2577, c2455, c2529, c2544, c2201, c2581, c69, c2585, c2032, c284, c2591, c102, c94, c2592, c5, c11, c2590, c290, c305, c2593, c953, c27, c948, c36, c324, c62, c349, c374, c196, c205, c203, c232, c126, c212, c179, c243, c147, c114] c2594 unsat2594 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2201 := derived2201 a h
  have h5 : Entails.eval a c2581 := derived2581 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c2585 := derived2585 a h
  have h8 : Entails.eval a c2032 := derived2032 a h
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c2591 := derived2591 a h
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c2592 := derived2592 a h
  have h14 : Entails.eval a c5 := h 4 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c2590 := derived2590 a h
  have h17 : Entails.eval a c290 := h 289 (by decide)
  have h18 : Entails.eval a c305 := h 304 (by decide)
  have h19 : Entails.eval a c2593 := derived2593 a h
  have h20 : Entails.eval a c953 := derived953 a h
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c948 := derived948 a h
  have h23 : Entails.eval a c36 := h 35 (by decide)
  have h24 : Entails.eval a c324 := h 323 (by decide)
  have h25 : Entails.eval a c62 := h 61 (by decide)
  have h26 : Entails.eval a c349 := h 348 (by decide)
  have h27 : Entails.eval a c374 := h 373 (by decide)
  have h28 : Entails.eval a c196 := h 195 (by decide)
  have h29 : Entails.eval a c205 := h 204 (by decide)
  have h30 : Entails.eval a c203 := h 202 (by decide)
  have h31 : Entails.eval a c232 := h 231 (by decide)
  have h32 : Entails.eval a c126 := h 125 (by decide)
  have h33 : Entails.eval a c212 := h 211 (by decide)
  have h34 : Entails.eval a c179 := h 178 (by decide)
  have h35 : Entails.eval a c243 := h 242 (by decide)
  have h36 : Entails.eval a c147 := h 146 (by decide)
  have h37 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2595 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2544, some c2201, some c2577, some c11, some c290, some c305, some c953, some c27, some c126, some c1480, some c117, some c202, some c1047, some c243, some c105, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p2595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2595 : lratChecker f2595 p2595 = .success := by decide +kernel
theorem unsat2595 : Unsatisfiable (PosFin 57) f2595 := by
  apply lratCheckerSound f2595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2595
  · intro a ha; simp [p2595] at ha; subst a; trivial
  · exact checked2595
theorem derived2595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2595 := by
  apply localUnsat_implies_entails f2595 [c2544, c2201, c2577, c11, c290, c305, c953, c27, c126, c1480, c117, c202, c1047, c243, c105] c2595 unsat2595 (by rfl) a
  have h0 : Entails.eval a c2544 := derived2544 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c305 := h 304 (by decide)
  have h6 : Entails.eval a c953 := derived953 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c1480 := derived1480 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c1047 := derived1047 a h
  have h13 : Entails.eval a c243 := h 242 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2596 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true), (⟨46, by decide⟩, true), (⟨38, by decide⟩, false), (⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c168, some c155, some c145, some c1047, some c107, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p2596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2596 : lratChecker f2596 p2596 = .success := by decide +kernel
theorem unsat2596 : Unsatisfiable (PosFin 57) f2596 := by
  apply lratCheckerSound f2596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2596
  · intro a ha; simp [p2596] at ha; subst a; trivial
  · exact checked2596
theorem derived2596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2596 := by
  apply localUnsat_implies_entails f2596 [c2577, c168, c155, c145, c1047, c107] c2596 unsat2596 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c1047 := derived1047 a h
  have h5 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2597 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c212, some c209, some c253, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p2597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2597 : lratChecker f2597 p2597 = .success := by decide +kernel
theorem unsat2597 : Unsatisfiable (PosFin 57) f2597 := by
  apply lratCheckerSound f2597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2597
  · intro a ha; simp [p2597] at ha; subst a; trivial
  · exact checked2597
theorem derived2597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2597 := by
  apply localUnsat_implies_entails f2597 [c212, c209, c253] c2597 unsat2597 (by rfl) a
  have h0 : Entails.eval a c212 := h 211 (by decide)
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2598 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2529, some c2577, some c2201, some c2544, some c2590, some c2585, some c2032, some c2581, some c69, some c305, some c284, some c36, some c324, some c2591, some c102, some c94, some c62, some c1463, some c374, some c290, some c330, some c341, some c349, some c2592, some c11, some c5, some c948, some c2593, some c953, some c2594, some c2595, some c179, some c120, some c157, some c2597, some c226, some c243, some c2596, some c234, some c1069, some c114, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42]]
theorem checked2598 : lratChecker f2598 p2598 = .success := by decide +kernel
theorem unsat2598 : Unsatisfiable (PosFin 57) f2598 := by
  apply lratCheckerSound f2598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2598
  · intro a ha; simp [p2598] at ha; subst a; trivial
  · exact checked2598
theorem derived2598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2598 := by
  apply localUnsat_implies_entails f2598 [c2455, c2529, c2577, c2201, c2544, c2590, c2585, c2032, c2581, c69, c305, c284, c36, c324, c2591, c102, c94, c62, c1463, c374, c290, c330, c341, c349, c2592, c11, c5, c948, c2593, c953, c2594, c2595, c179, c120, c157, c2597, c226, c243, c2596, c234, c1069, c114] c2598 unsat2598 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2201 := derived2201 a h
  have h4 : Entails.eval a c2544 := derived2544 a h
  have h5 : Entails.eval a c2590 := derived2590 a h
  have h6 : Entails.eval a c2585 := derived2585 a h
  have h7 : Entails.eval a c2032 := derived2032 a h
  have h8 : Entails.eval a c2581 := derived2581 a h
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c2591 := derived2591 a h
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c62 := h 61 (by decide)
  have h18 : Entails.eval a c1463 := derived1463 a h
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c290 := h 289 (by decide)
  have h21 : Entails.eval a c330 := h 329 (by decide)
  have h22 : Entails.eval a c341 := h 340 (by decide)
  have h23 : Entails.eval a c349 := h 348 (by decide)
  have h24 : Entails.eval a c2592 := derived2592 a h
  have h25 : Entails.eval a c11 := h 10 (by decide)
  have h26 : Entails.eval a c5 := h 4 (by decide)
  have h27 : Entails.eval a c948 := derived948 a h
  have h28 : Entails.eval a c2593 := derived2593 a h
  have h29 : Entails.eval a c953 := derived953 a h
  have h30 : Entails.eval a c2594 := derived2594 a h
  have h31 : Entails.eval a c2595 := derived2595 a h
  have h32 : Entails.eval a c179 := h 178 (by decide)
  have h33 : Entails.eval a c120 := h 119 (by decide)
  have h34 : Entails.eval a c157 := h 156 (by decide)
  have h35 : Entails.eval a c2597 := derived2597 a h
  have h36 : Entails.eval a c226 := h 225 (by decide)
  have h37 : Entails.eval a c243 := h 242 (by decide)
  have h38 : Entails.eval a c2596 := derived2596 a h
  have h39 : Entails.eval a c234 := h 233 (by decide)
  have h40 : Entails.eval a c1069 := derived1069 a h
  have h41 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2599 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2529, some c2598, some c2590, some c2581, some c374, some c290, some c95, some c50, some c102, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2599 : lratChecker f2599 p2599 = .success := by decide +kernel
theorem unsat2599 : Unsatisfiable (PosFin 57) f2599 := by
  apply lratCheckerSound f2599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2599
  · intro a ha; simp [p2599] at ha; subst a; trivial
  · exact checked2599
theorem derived2599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2599 := by
  apply localUnsat_implies_entails f2599 [c2577, c2529, c2598, c2590, c2581, c374, c290, c95, c50, c102] c2599 unsat2599 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2598 := derived2598 a h
  have h3 : Entails.eval a c2590 := derived2590 a h
  have h4 : Entails.eval a c2581 := derived2581 a h
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2600 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2577, some c2581, some c2590, some c2598, some c2599, some c94, some c102, some c95, some c51, some c292, some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2600 : lratChecker f2600 p2600 = .success := by decide +kernel
theorem unsat2600 : Unsatisfiable (PosFin 57) f2600 := by
  apply lratCheckerSound f2600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2600
  · intro a ha; simp [p2600] at ha; subst a; trivial
  · exact checked2600
theorem derived2600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2600 := by
  apply localUnsat_implies_entails f2600 [c2529, c2577, c2581, c2590, c2598, c2599, c94, c102, c95, c51, c292] c2600 unsat2600 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c2581 := derived2581 a h
  have h3 : Entails.eval a c2590 := derived2590 a h
  have h4 : Entails.eval a c2598 := derived2598 a h
  have h5 : Entails.eval a c2599 := derived2599 a h
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2601 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2600, some c2529, some c2577, some c2455, some c2034, some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2601 : lratChecker f2601 p2601 = .success := by decide +kernel
theorem unsat2601 : Unsatisfiable (PosFin 57) f2601 := by
  apply lratCheckerSound f2601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2601
  · intro a ha; simp [p2601] at ha; subst a; trivial
  · exact checked2601
theorem derived2601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2601 := by
  apply localUnsat_implies_entails f2601 [c2600, c2529, c2577, c2455, c2034] c2601 unsat2601 (by rfl) a
  have h0 : Entails.eval a c2600 := derived2600 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2455 := derived2455 a h
  have h4 : Entails.eval a c2034 := derived2034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2602 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2600, some c2577, some c373, some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2602 : lratChecker f2602 p2602 = .success := by decide +kernel
theorem unsat2602 : Unsatisfiable (PosFin 57) f2602 := by
  apply lratCheckerSound f2602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2602
  · intro a ha; simp [p2602] at ha; subst a; trivial
  · exact checked2602
theorem derived2602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2602 := by
  apply localUnsat_implies_entails f2602 [c2600, c2577, c373] c2602 unsat2602 (by rfl) a
  have h0 : Entails.eval a c2600 := derived2600 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2603 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2601, some c2455, some c68, some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2603 : lratChecker f2603 p2603 = .success := by decide +kernel
theorem unsat2603 : Unsatisfiable (PosFin 57) f2603 := by
  apply lratCheckerSound f2603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2603
  · intro a ha; simp [p2603] at ha; subst a; trivial
  · exact checked2603
theorem derived2603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2603 := by
  apply localUnsat_implies_entails f2603 [c2601, c2455, c68] c2603 unsat2603 (by rfl) a
  have h0 : Entails.eval a c2601 := derived2601 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2604 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2600, some c2455, some c2603, some c2529, some c2059, some c2025, some c329, some c37, some c284, some c2064, some c76, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2604 : lratChecker f2604 p2604 = .success := by decide +kernel
theorem unsat2604 : Unsatisfiable (PosFin 57) f2604 := by
  apply lratCheckerSound f2604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2604
  · intro a ha; simp [p2604] at ha; subst a; trivial
  · exact checked2604
theorem derived2604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2604 := by
  apply localUnsat_implies_entails f2604 [c2577, c2600, c2455, c2603, c2529, c2059, c2025, c329, c37, c284, c2064, c76] c2604 unsat2604 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2600 := derived2600 a h
  have h2 : Entails.eval a c2455 := derived2455 a h
  have h3 : Entails.eval a c2603 := derived2603 a h
  have h4 : Entails.eval a c2529 := derived2529 a h
  have h5 : Entails.eval a c2059 := derived2059 a h
  have h6 : Entails.eval a c2025 := derived2025 a h
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c2064 := derived2064 a h
  have h11 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2605 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2600, some c2603, some c2529, some c2577, some c2601, some c2455, some c2604, some c2059, some c2025, some c329, some c37, some c284, some c2018, some c374, some c102, some c93, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2605 : lratChecker f2605 p2605 = .success := by decide +kernel
theorem unsat2605 : Unsatisfiable (PosFin 57) f2605 := by
  apply lratCheckerSound f2605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2605
  · intro a ha; simp [p2605] at ha; subst a; trivial
  · exact checked2605
theorem derived2605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2605 := by
  apply localUnsat_implies_entails f2605 [c2600, c2603, c2529, c2577, c2601, c2455, c2604, c2059, c2025, c329, c37, c284, c2018, c374, c102, c93] c2605 unsat2605 (by rfl) a
  have h0 : Entails.eval a c2600 := derived2600 a h
  have h1 : Entails.eval a c2603 := derived2603 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2577 := derived2577 a h
  have h4 : Entails.eval a c2601 := derived2601 a h
  have h5 : Entails.eval a c2455 := derived2455 a h
  have h6 : Entails.eval a c2604 := derived2604 a h
  have h7 : Entails.eval a c2059 := derived2059 a h
  have h8 : Entails.eval a c2025 := derived2025 a h
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c2018 := derived2018 a h
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2606 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2601, some c2577, some c2600, some c2529, some c1079, some c93, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p2606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2606 : lratChecker f2606 p2606 = .success := by decide +kernel
theorem unsat2606 : Unsatisfiable (PosFin 57) f2606 := by
  apply lratCheckerSound f2606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2606
  · intro a ha; simp [p2606] at ha; subst a; trivial
  · exact checked2606
theorem derived2606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2606 := by
  apply localUnsat_implies_entails f2606 [c2455, c2601, c2577, c2600, c2529, c1079, c93] c2606 unsat2606 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2601 := derived2601 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2600 := derived2600 a h
  have h4 : Entails.eval a c2529 := derived2529 a h
  have h5 : Entails.eval a c1079 := derived1079 a h
  have h6 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2607 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2602, some c2601, some c2201, some c176, some c177, some c16, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p2607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2607 : lratChecker f2607 p2607 = .success := by decide +kernel
theorem unsat2607 : Unsatisfiable (PosFin 57) f2607 := by
  apply lratCheckerSound f2607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2607
  · intro a ha; simp [p2607] at ha; subst a; trivial
  · exact checked2607
theorem derived2607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2607 := by
  apply localUnsat_implies_entails f2607 [c2602, c2601, c2201, c176, c177, c16] c2607 unsat2607 (by rfl) a
  have h0 : Entails.eval a c2602 := derived2602 a h
  have h1 : Entails.eval a c2601 := derived2601 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c177 := h 176 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2608 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨56, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2603, some c2602, some c2201, some c2600, some c2577, some c2605, some c2025, some c2606, some c2607, some c2604, some c102, some c70, some c369, some c2059, some c329, some c37, some c284, some c128, some c160, some c185, some c180, some c8, some c156, some c62, some c346, some c1886, some c237, some c235, some c219, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked2608 : lratChecker f2608 p2608 = .success := by decide +kernel
theorem unsat2608 : Unsatisfiable (PosFin 57) f2608 := by
  apply lratCheckerSound f2608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2608
  · intro a ha; simp [p2608] at ha; subst a; trivial
  · exact checked2608
theorem derived2608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2608 := by
  apply localUnsat_implies_entails f2608 [c2529, c2455, c2603, c2602, c2201, c2600, c2577, c2605, c2025, c2606, c2607, c2604, c102, c70, c369, c2059, c329, c37, c284, c128, c160, c185, c180, c8, c156, c62, c346, c1886, c237, c235, c219] c2608 unsat2608 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2603 := derived2603 a h
  have h3 : Entails.eval a c2602 := derived2602 a h
  have h4 : Entails.eval a c2201 := derived2201 a h
  have h5 : Entails.eval a c2600 := derived2600 a h
  have h6 : Entails.eval a c2577 := derived2577 a h
  have h7 : Entails.eval a c2605 := derived2605 a h
  have h8 : Entails.eval a c2025 := derived2025 a h
  have h9 : Entails.eval a c2606 := derived2606 a h
  have h10 : Entails.eval a c2607 := derived2607 a h
  have h11 : Entails.eval a c2604 := derived2604 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c369 := h 368 (by decide)
  have h15 : Entails.eval a c2059 := derived2059 a h
  have h16 : Entails.eval a c329 := h 328 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c284 := h 283 (by decide)
  have h19 : Entails.eval a c128 := h 127 (by decide)
  have h20 : Entails.eval a c160 := h 159 (by decide)
  have h21 : Entails.eval a c185 := h 184 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  have h23 : Entails.eval a c8 := h 7 (by decide)
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c62 := h 61 (by decide)
  have h26 : Entails.eval a c346 := h 345 (by decide)
  have h27 : Entails.eval a c1886 := derived1886 a h
  have h28 : Entails.eval a c237 := h 236 (by decide)
  have h29 : Entails.eval a c235 := h 234 (by decide)
  have h30 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2609 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2577, some c2600, some c2529, some c2455, some c2603, some c2544, some c2605, some c2604, some c2025, some c2606, some c102, some c70, some c369, some c2059, some c329, some c37, some c284, some c2607, some c128, some c160, some c122, some c2608, some c1031, some c197, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2609 : lratChecker f2609 p2609 = .success := by decide +kernel
theorem unsat2609 : Unsatisfiable (PosFin 57) f2609 := by
  apply lratCheckerSound f2609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2609
  · intro a ha; simp [p2609] at ha; subst a; trivial
  · exact checked2609
theorem derived2609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2609 := by
  apply localUnsat_implies_entails f2609 [c2577, c2600, c2529, c2455, c2603, c2544, c2605, c2604, c2025, c2606, c102, c70, c369, c2059, c329, c37, c284, c2607, c128, c160, c122, c2608, c1031, c197] c2609 unsat2609 (by rfl) a
  have h0 : Entails.eval a c2577 := derived2577 a h
  have h1 : Entails.eval a c2600 := derived2600 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2455 := derived2455 a h
  have h4 : Entails.eval a c2603 := derived2603 a h
  have h5 : Entails.eval a c2544 := derived2544 a h
  have h6 : Entails.eval a c2605 := derived2605 a h
  have h7 : Entails.eval a c2604 := derived2604 a h
  have h8 : Entails.eval a c2025 := derived2025 a h
  have h9 : Entails.eval a c2606 := derived2606 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c2059 := derived2059 a h
  have h14 : Entails.eval a c329 := h 328 (by decide)
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c284 := h 283 (by decide)
  have h17 : Entails.eval a c2607 := derived2607 a h
  have h18 : Entails.eval a c128 := h 127 (by decide)
  have h19 : Entails.eval a c160 := h 159 (by decide)
  have h20 : Entails.eval a c122 := h 121 (by decide)
  have h21 : Entails.eval a c2608 := derived2608 a h
  have h22 : Entails.eval a c1031 := derived1031 a h
  have h23 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2610 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2600, some c2529, some c2601, some c2602, some c2201, some c2603, some c2577, some c2609, some c2604, some c2025, some c2606, some c102, some c2605, some c70, some c2490, some c329, some c37, some c2059, some c128, some c176, some c16, some c181, some c158, some c992, some c1243, some c240, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2610 : lratChecker f2610 p2610 = .success := by decide +kernel
theorem unsat2610 : Unsatisfiable (PosFin 57) f2610 := by
  apply lratCheckerSound f2610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2610
  · intro a ha; simp [p2610] at ha; subst a; trivial
  · exact checked2610
theorem derived2610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2610 := by
  apply localUnsat_implies_entails f2610 [c2455, c2600, c2529, c2601, c2602, c2201, c2603, c2577, c2609, c2604, c2025, c2606, c102, c2605, c70, c2490, c329, c37, c2059, c128, c176, c16, c181, c158, c992, c1243, c240] c2610 unsat2610 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2600 := derived2600 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c2601 := derived2601 a h
  have h4 : Entails.eval a c2602 := derived2602 a h
  have h5 : Entails.eval a c2201 := derived2201 a h
  have h6 : Entails.eval a c2603 := derived2603 a h
  have h7 : Entails.eval a c2577 := derived2577 a h
  have h8 : Entails.eval a c2609 := derived2609 a h
  have h9 : Entails.eval a c2604 := derived2604 a h
  have h10 : Entails.eval a c2025 := derived2025 a h
  have h11 : Entails.eval a c2606 := derived2606 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c2605 := derived2605 a h
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c2490 := derived2490 a h
  have h16 : Entails.eval a c329 := h 328 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c2059 := derived2059 a h
  have h19 : Entails.eval a c128 := h 127 (by decide)
  have h20 : Entails.eval a c176 := h 175 (by decide)
  have h21 : Entails.eval a c16 := h 15 (by decide)
  have h22 : Entails.eval a c181 := h 180 (by decide)
  have h23 : Entails.eval a c158 := h 157 (by decide)
  have h24 : Entails.eval a c992 := derived992 a h
  have h25 : Entails.eval a c1243 := derived1243 a h
  have h26 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2611 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2544, some c2577, some c2600, some c2529, some c2603, some c2455, some c2059, some c2025, some c329, some c37, some c284, some c2606, some c2604, some c2605, some c102, some c70, some c369, some c160, some c8, some c167, some c1031, some c62, some c346, some c219, some c212, some c235, some c139, some c114, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2611 : lratChecker f2611 p2611 = .success := by decide +kernel
theorem unsat2611 : Unsatisfiable (PosFin 57) f2611 := by
  apply lratCheckerSound f2611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2611
  · intro a ha; simp [p2611] at ha; subst a; trivial
  · exact checked2611
theorem derived2611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2611 := by
  apply localUnsat_implies_entails f2611 [c2544, c2577, c2600, c2529, c2603, c2455, c2059, c2025, c329, c37, c284, c2606, c2604, c2605, c102, c70, c369, c160, c8, c167, c1031, c62, c346, c219, c212, c235, c139, c114] c2611 unsat2611 (by rfl) a
  have h0 : Entails.eval a c2544 := derived2544 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c2600 := derived2600 a h
  have h3 : Entails.eval a c2529 := derived2529 a h
  have h4 : Entails.eval a c2603 := derived2603 a h
  have h5 : Entails.eval a c2455 := derived2455 a h
  have h6 : Entails.eval a c2059 := derived2059 a h
  have h7 : Entails.eval a c2025 := derived2025 a h
  have h8 : Entails.eval a c329 := h 328 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c2606 := derived2606 a h
  have h12 : Entails.eval a c2604 := derived2604 a h
  have h13 : Entails.eval a c2605 := derived2605 a h
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c1031 := derived1031 a h
  have h21 : Entails.eval a c62 := h 61 (by decide)
  have h22 : Entails.eval a c346 := h 345 (by decide)
  have h23 : Entails.eval a c219 := h 218 (by decide)
  have h24 : Entails.eval a c212 := h 211 (by decide)
  have h25 : Entails.eval a c235 := h 234 (by decide)
  have h26 : Entails.eval a c139 := h 138 (by decide)
  have h27 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2612 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2529, some c2455, some c2603, some c2544, some c2577, some c2601, some c2602, some c2600, some c2201, some c2609, some c2605, some c2604, some c2025, some c2606, some c102, some c70, some c369, some c2490, some c2059, some c329, some c37, some c311, some c284, some c2610, some c160, some c8, some c1031, some c1888, some c198, some c197, some c122, some c176, some c2611, some c246, some c259, some c151, some c174, some c107, some c990, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]]
theorem checked2612 : lratChecker f2612 p2612 = .success := by decide +kernel
theorem unsat2612 : Unsatisfiable (PosFin 57) f2612 := by
  apply lratCheckerSound f2612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2612
  · intro a ha; simp [p2612] at ha; subst a; trivial
  · exact checked2612
theorem derived2612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2612 := by
  apply localUnsat_implies_entails f2612 [c2529, c2455, c2603, c2544, c2577, c2601, c2602, c2600, c2201, c2609, c2605, c2604, c2025, c2606, c102, c70, c369, c2490, c2059, c329, c37, c311, c284, c2610, c160, c8, c1031, c1888, c198, c197, c122, c176, c2611, c246, c259, c151, c174, c107, c990] c2612 unsat2612 (by rfl) a
  have h0 : Entails.eval a c2529 := derived2529 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2603 := derived2603 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c2577 := derived2577 a h
  have h5 : Entails.eval a c2601 := derived2601 a h
  have h6 : Entails.eval a c2602 := derived2602 a h
  have h7 : Entails.eval a c2600 := derived2600 a h
  have h8 : Entails.eval a c2201 := derived2201 a h
  have h9 : Entails.eval a c2609 := derived2609 a h
  have h10 : Entails.eval a c2605 := derived2605 a h
  have h11 : Entails.eval a c2604 := derived2604 a h
  have h12 : Entails.eval a c2025 := derived2025 a h
  have h13 : Entails.eval a c2606 := derived2606 a h
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c2490 := derived2490 a h
  have h18 : Entails.eval a c2059 := derived2059 a h
  have h19 : Entails.eval a c329 := h 328 (by decide)
  have h20 : Entails.eval a c37 := h 36 (by decide)
  have h21 : Entails.eval a c311 := h 310 (by decide)
  have h22 : Entails.eval a c284 := h 283 (by decide)
  have h23 : Entails.eval a c2610 := derived2610 a h
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c8 := h 7 (by decide)
  have h26 : Entails.eval a c1031 := derived1031 a h
  have h27 : Entails.eval a c1888 := derived1888 a h
  have h28 : Entails.eval a c198 := h 197 (by decide)
  have h29 : Entails.eval a c197 := h 196 (by decide)
  have h30 : Entails.eval a c122 := h 121 (by decide)
  have h31 : Entails.eval a c176 := h 175 (by decide)
  have h32 : Entails.eval a c2611 := derived2611 a h
  have h33 : Entails.eval a c246 := h 245 (by decide)
  have h34 : Entails.eval a c259 := h 258 (by decide)
  have h35 : Entails.eval a c151 := h 150 (by decide)
  have h36 : Entails.eval a c174 := h 173 (by decide)
  have h37 : Entails.eval a c107 := h 106 (by decide)
  have h38 : Entails.eval a c990 := derived990 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2613 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2455, some c2600, some c2577, some c2529, some c2603, some c2544, some c2601, some c2602, some c2025, some c2059, some c329, some c37, some c284, some c2604, some c2605, some c2606, some c102, some c70, some c369, some c2612, some c5, some c1480, some c160, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p2613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2613 : lratChecker f2613 p2613 = .success := by decide +kernel
theorem unsat2613 : Unsatisfiable (PosFin 57) f2613 := by
  apply lratCheckerSound f2613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2613
  · intro a ha; simp [p2613] at ha; subst a; trivial
  · exact checked2613
theorem derived2613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2613 := by
  apply localUnsat_implies_entails f2613 [c2455, c2600, c2577, c2529, c2603, c2544, c2601, c2602, c2025, c2059, c329, c37, c284, c2604, c2605, c2606, c102, c70, c369, c2612, c5, c1480, c160] c2613 unsat2613 (by rfl) a
  have h0 : Entails.eval a c2455 := derived2455 a h
  have h1 : Entails.eval a c2600 := derived2600 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2529 := derived2529 a h
  have h4 : Entails.eval a c2603 := derived2603 a h
  have h5 : Entails.eval a c2544 := derived2544 a h
  have h6 : Entails.eval a c2601 := derived2601 a h
  have h7 : Entails.eval a c2602 := derived2602 a h
  have h8 : Entails.eval a c2025 := derived2025 a h
  have h9 : Entails.eval a c2059 := derived2059 a h
  have h10 : Entails.eval a c329 := h 328 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c2604 := derived2604 a h
  have h14 : Entails.eval a c2605 := derived2605 a h
  have h15 : Entails.eval a c2606 := derived2606 a h
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c2612 := derived2612 a h
  have h20 : Entails.eval a c5 := h 4 (by decide)
  have h21 : Entails.eval a c1480 := derived1480 a h
  have h22 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2614 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2613, some c2577, some c2600, some c289, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p2614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2614 : lratChecker f2614 p2614 = .success := by decide +kernel
theorem unsat2614 : Unsatisfiable (PosFin 57) f2614 := by
  apply lratCheckerSound f2614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2614
  · intro a ha; simp [p2614] at ha; subst a; trivial
  · exact checked2614
theorem derived2614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2614 := by
  apply localUnsat_implies_entails f2614 [c2613, c2577, c2600, c289] c2614 unsat2614 (by rfl) a
  have h0 : Entails.eval a c2613 := derived2613 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c2600 := derived2600 a h
  have h3 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2615 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2613, some c2600, some c2577, some c2538, some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p2615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2615 : lratChecker f2615 p2615 = .success := by decide +kernel
theorem unsat2615 : Unsatisfiable (PosFin 57) f2615 := by
  apply lratCheckerSound f2615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2615
  · intro a ha; simp [p2615] at ha; subst a; trivial
  · exact checked2615
theorem derived2615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2615 := by
  apply localUnsat_implies_entails f2615 [c2613, c2600, c2577, c2538] c2615 unsat2615 (by rfl) a
  have h0 : Entails.eval a c2613 := derived2613 a h
  have h1 : Entails.eval a c2600 := derived2600 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2538 := derived2538 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2616 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2614, some c2529, some c37, some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p2616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2616 : lratChecker f2616 p2616 = .success := by decide +kernel
theorem unsat2616 : Unsatisfiable (PosFin 57) f2616 := by
  apply lratCheckerSound f2616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2616
  · intro a ha; simp [p2616] at ha; subst a; trivial
  · exact checked2616
theorem derived2616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2616 := by
  apply localUnsat_implies_entails f2616 [c2614, c2529, c37] c2616 unsat2616 (by rfl) a
  have h0 : Entails.eval a c2614 := derived2614 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2617 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2615, some c2455, some c2033, some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p2617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2617 : lratChecker f2617 p2617 = .success := by decide +kernel
theorem unsat2617 : Unsatisfiable (PosFin 57) f2617 := by
  apply lratCheckerSound f2617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2617
  · intro a ha; simp [p2617] at ha; subst a; trivial
  · exact checked2617
theorem derived2617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2617 := by
  apply localUnsat_implies_entails f2617 [c2615, c2455, c2033] c2617 unsat2617 (by rfl) a
  have h0 : Entails.eval a c2615 := derived2615 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2618 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2617, some c2616, some c2603, some c324, some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p2618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2618 : lratChecker f2618 p2618 = .success := by decide +kernel
theorem unsat2618 : Unsatisfiable (PosFin 57) f2618 := by
  apply lratCheckerSound f2618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2618
  · intro a ha; simp [p2618] at ha; subst a; trivial
  · exact checked2618
theorem derived2618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2618 := by
  apply localUnsat_implies_entails f2618 [c2617, c2616, c2603, c324] c2618 unsat2618 (by rfl) a
  have h0 : Entails.eval a c2617 := derived2617 a h
  have h1 : Entails.eval a c2616 := derived2616 a h
  have h2 : Entails.eval a c2603 := derived2603 a h
  have h3 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2619 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2617, some c2616, some c351, some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p2619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2619 : lratChecker f2619 p2619 = .success := by decide +kernel
theorem unsat2619 : Unsatisfiable (PosFin 57) f2619 := by
  apply lratCheckerSound f2619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2619
  · intro a ha; simp [p2619] at ha; subst a; trivial
  · exact checked2619
theorem derived2619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2619 := by
  apply localUnsat_implies_entails f2619 [c2617, c2616, c351] c2619 unsat2619 (by rfl) a
  have h0 : Entails.eval a c2617 := derived2617 a h
  have h1 : Entails.eval a c2616 := derived2616 a h
  have h2 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2620 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2618, some c2603, some c2577, some c2529, some c2617, some c76, some c2220, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2620 : lratChecker f2620 p2620 = .success := by decide +kernel
theorem unsat2620 : Unsatisfiable (PosFin 57) f2620 := by
  apply lratCheckerSound f2620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2620
  · intro a ha; simp [p2620] at ha; subst a; trivial
  · exact checked2620
theorem derived2620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2620 := by
  apply localUnsat_implies_entails f2620 [c2618, c2603, c2577, c2529, c2617, c76, c2220] c2620 unsat2620 (by rfl) a
  have h0 : Entails.eval a c2618 := derived2618 a h
  have h1 : Entails.eval a c2603 := derived2603 a h
  have h2 : Entails.eval a c2577 := derived2577 a h
  have h3 : Entails.eval a c2529 := derived2529 a h
  have h4 : Entails.eval a c2617 := derived2617 a h
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c2220 := derived2220 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2621 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2614, some c2201, some c2600, some c2577, some c2602, some c2615, some c2617, some c2620, some c2544, some c2618, some c2603, some c2613, some c2529, some c2616, some c2607, some c144, some c102, some c50, some c2351, some c82, some c306, some c369, some c160, some c8, some c1031, some c138, some c185, some c156, some c209, some c180, some c237, some c1886, some c207, some c235, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p2621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked2621 : lratChecker f2621 p2621 = .success := by decide +kernel
theorem unsat2621 : Unsatisfiable (PosFin 57) f2621 := by
  apply lratCheckerSound f2621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2621
  · intro a ha; simp [p2621] at ha; subst a; trivial
  · exact checked2621
theorem derived2621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2621 := by
  apply localUnsat_implies_entails f2621 [c2614, c2201, c2600, c2577, c2602, c2615, c2617, c2620, c2544, c2618, c2603, c2613, c2529, c2616, c2607, c144, c102, c50, c2351, c82, c306, c369, c160, c8, c1031, c138, c185, c156, c209, c180, c237, c1886, c207, c235] c2621 unsat2621 (by rfl) a
  have h0 : Entails.eval a c2614 := derived2614 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2600 := derived2600 a h
  have h3 : Entails.eval a c2577 := derived2577 a h
  have h4 : Entails.eval a c2602 := derived2602 a h
  have h5 : Entails.eval a c2615 := derived2615 a h
  have h6 : Entails.eval a c2617 := derived2617 a h
  have h7 : Entails.eval a c2620 := derived2620 a h
  have h8 : Entails.eval a c2544 := derived2544 a h
  have h9 : Entails.eval a c2618 := derived2618 a h
  have h10 : Entails.eval a c2603 := derived2603 a h
  have h11 : Entails.eval a c2613 := derived2613 a h
  have h12 : Entails.eval a c2529 := derived2529 a h
  have h13 : Entails.eval a c2616 := derived2616 a h
  have h14 : Entails.eval a c2607 := derived2607 a h
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c2351 := derived2351 a h
  have h19 : Entails.eval a c82 := h 81 (by decide)
  have h20 : Entails.eval a c306 := h 305 (by decide)
  have h21 : Entails.eval a c369 := h 368 (by decide)
  have h22 : Entails.eval a c160 := h 159 (by decide)
  have h23 : Entails.eval a c8 := h 7 (by decide)
  have h24 : Entails.eval a c1031 := derived1031 a h
  have h25 : Entails.eval a c138 := h 137 (by decide)
  have h26 : Entails.eval a c185 := h 184 (by decide)
  have h27 : Entails.eval a c156 := h 155 (by decide)
  have h28 : Entails.eval a c209 := h 208 (by decide)
  have h29 : Entails.eval a c180 := h 179 (by decide)
  have h30 : Entails.eval a c237 := h 236 (by decide)
  have h31 : Entails.eval a c1886 := derived1886 a h
  have h32 : Entails.eval a c207 := h 206 (by decide)
  have h33 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2622 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2601, some c2455, some c93, some c2621, some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p2622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2622 : lratChecker f2622 p2622 = .success := by decide +kernel
theorem unsat2622 : Unsatisfiable (PosFin 57) f2622 := by
  apply lratCheckerSound f2622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2622
  · intro a ha; simp [p2622] at ha; subst a; trivial
  · exact checked2622
theorem derived2622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2622 := by
  apply localUnsat_implies_entails f2622 [c2601, c2455, c93, c2621] c2622 unsat2622 (by rfl) a
  have h0 : Entails.eval a c2601 := derived2601 a h
  have h1 : Entails.eval a c2455 := derived2455 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c2621 := derived2621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2623 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2622, some c2577, some c374, some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2623 : lratChecker f2623 p2623 = .success := by decide +kernel
theorem unsat2623 : Unsatisfiable (PosFin 57) f2623 := by
  apply lratCheckerSound f2623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2623
  · intro a ha; simp [p2623] at ha; subst a; trivial
  · exact checked2623
theorem derived2623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2623 := by
  apply localUnsat_implies_entails f2623 [c2622, c2577, c374] c2623 unsat2623 (by rfl) a
  have h0 : Entails.eval a c2622 := derived2622 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2624 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2622, some c2613, some c2600, some c2529, some c2577, some c1078, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p2624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2624 : lratChecker f2624 p2624 = .success := by decide +kernel
theorem unsat2624 : Unsatisfiable (PosFin 57) f2624 := by
  apply lratCheckerSound f2624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2624
  · intro a ha; simp [p2624] at ha; subst a; trivial
  · exact checked2624
theorem derived2624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2624 := by
  apply localUnsat_implies_entails f2624 [c2622, c2613, c2600, c2529, c2577, c1078] c2624 unsat2624 (by rfl) a
  have h0 : Entails.eval a c2622 := derived2622 a h
  have h1 : Entails.eval a c2613 := derived2613 a h
  have h2 : Entails.eval a c2600 := derived2600 a h
  have h3 : Entails.eval a c2529 := derived2529 a h
  have h4 : Entails.eval a c2577 := derived2577 a h
  have h5 : Entails.eval a c1078 := derived1078 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2625 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2624, some c2620, some c102, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2625 : lratChecker f2625 p2625 = .success := by decide +kernel
theorem unsat2625 : Unsatisfiable (PosFin 57) f2625 := by
  apply lratCheckerSound f2625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2625
  · intro a ha; simp [p2625] at ha; subst a; trivial
  · exact checked2625
theorem derived2625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2625 := by
  apply localUnsat_implies_entails f2625 [c2624, c2620, c102] c2625 unsat2625 (by rfl) a
  have h0 : Entails.eval a c2624 := derived2624 a h
  have h1 : Entails.eval a c2620 := derived2620 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2626 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2625, some c2529, some c2614, some c50, some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p2626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2626 : lratChecker f2626 p2626 = .success := by decide +kernel
theorem unsat2626 : Unsatisfiable (PosFin 57) f2626 := by
  apply lratCheckerSound f2626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2626
  · intro a ha; simp [p2626] at ha; subst a; trivial
  · exact checked2626
theorem derived2626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2626 := by
  apply localUnsat_implies_entails f2626 [c2625, c2529, c2614, c50] c2626 unsat2626 (by rfl) a
  have h0 : Entails.eval a c2625 := derived2625 a h
  have h1 : Entails.eval a c2529 := derived2529 a h
  have h2 : Entails.eval a c2614 := derived2614 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2627 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2625, some c2618, some c2529, some c82, some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p2627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2627 : lratChecker f2627 p2627 = .success := by decide +kernel
theorem unsat2627 : Unsatisfiable (PosFin 57) f2627 := by
  apply lratCheckerSound f2627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2627
  · intro a ha; simp [p2627] at ha; subst a; trivial
  · exact checked2627
theorem derived2627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2627 := by
  apply localUnsat_implies_entails f2627 [c2625, c2618, c2529, c82] c2627 unsat2627 (by rfl) a
  have h0 : Entails.eval a c2625 := derived2625 a h
  have h1 : Entails.eval a c2618 := derived2618 a h
  have h2 : Entails.eval a c2529 := derived2529 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2628 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2627, some c2626, some c2613, some c274, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2628 : lratChecker f2628 p2628 = .success := by decide +kernel
theorem unsat2628 : Unsatisfiable (PosFin 57) f2628 := by
  apply lratCheckerSound f2628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2628
  · intro a ha; simp [p2628] at ha; subst a; trivial
  · exact checked2628
theorem derived2628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2628 := by
  apply localUnsat_implies_entails f2628 [c2627, c2626, c2613, c274] c2628 unsat2628 (by rfl) a
  have h0 : Entails.eval a c2627 := derived2627 a h
  have h1 : Entails.eval a c2626 := derived2626 a h
  have h2 : Entails.eval a c2613 := derived2613 a h
  have h3 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2629 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2627, some c2603, some c369, some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p2629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2629 : lratChecker f2629 p2629 = .success := by decide +kernel
theorem unsat2629 : Unsatisfiable (PosFin 57) f2629 := by
  apply lratCheckerSound f2629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2629
  · intro a ha; simp [p2629] at ha; subst a; trivial
  · exact checked2629
theorem derived2629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2629 := by
  apply localUnsat_implies_entails f2629 [c2627, c2603, c369] c2629 unsat2629 (by rfl) a
  have h0 : Entails.eval a c2627 := derived2627 a h
  have h1 : Entails.eval a c2603 := derived2603 a h
  have h2 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2630 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2627, some c2603, some c2617, some c325, some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p2630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2630 : lratChecker f2630 p2630 = .success := by decide +kernel
theorem unsat2630 : Unsatisfiable (PosFin 57) f2630 := by
  apply lratCheckerSound f2630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2630
  · intro a ha; simp [p2630] at ha; subst a; trivial
  · exact checked2630
theorem derived2630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2630 := by
  apply localUnsat_implies_entails f2630 [c2627, c2603, c2617, c325] c2630 unsat2630 (by rfl) a
  have h0 : Entails.eval a c2627 := derived2627 a h
  have h1 : Entails.eval a c2603 := derived2603 a h
  have h2 : Entails.eval a c2617 := derived2617 a h
  have h3 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2631 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2617, some c2616, some c2601, some c2602, some c2624, some c2201, some c2628, some c2603, some c2577, some c2622, some c1480, some c144, some c176, some c16, some c181, some c158, some c1243, some c992, some c240, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p2631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2631 : lratChecker f2631 p2631 = .success := by decide +kernel
theorem unsat2631 : Unsatisfiable (PosFin 57) f2631 := by
  apply lratCheckerSound f2631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2631
  · intro a ha; simp [p2631] at ha; subst a; trivial
  · exact checked2631
theorem derived2631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2631 := by
  apply localUnsat_implies_entails f2631 [c2617, c2616, c2601, c2602, c2624, c2201, c2628, c2603, c2577, c2622, c1480, c144, c176, c16, c181, c158, c1243, c992, c240] c2631 unsat2631 (by rfl) a
  have h0 : Entails.eval a c2617 := derived2617 a h
  have h1 : Entails.eval a c2616 := derived2616 a h
  have h2 : Entails.eval a c2601 := derived2601 a h
  have h3 : Entails.eval a c2602 := derived2602 a h
  have h4 : Entails.eval a c2624 := derived2624 a h
  have h5 : Entails.eval a c2201 := derived2201 a h
  have h6 : Entails.eval a c2628 := derived2628 a h
  have h7 : Entails.eval a c2603 := derived2603 a h
  have h8 : Entails.eval a c2577 := derived2577 a h
  have h9 : Entails.eval a c2622 := derived2622 a h
  have h10 : Entails.eval a c1480 := derived1480 a h
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c1243 := derived1243 a h
  have h17 : Entails.eval a c992 := derived992 a h
  have h18 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2632 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2631, some c2618, some c2629, some c160, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2632 : lratChecker f2632 p2632 = .success := by decide +kernel
theorem unsat2632 : Unsatisfiable (PosFin 57) f2632 := by
  apply lratCheckerSound f2632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2632
  · intro a ha; simp [p2632] at ha; subst a; trivial
  · exact checked2632
theorem derived2632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2632 := by
  apply localUnsat_implies_entails f2632 [c2631, c2618, c2629, c160] c2632 unsat2632 (by rfl) a
  have h0 : Entails.eval a c2631 := derived2631 a h
  have h1 : Entails.eval a c2618 := derived2618 a h
  have h2 : Entails.eval a c2629 := derived2629 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2633 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2632, some c2620, some c2544, some c5, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p2633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2633 : lratChecker f2633 p2633 = .success := by decide +kernel
theorem unsat2633 : Unsatisfiable (PosFin 57) f2633 := by
  apply lratCheckerSound f2633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2633
  · intro a ha; simp [p2633] at ha; subst a; trivial
  · exact checked2633
theorem derived2633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2633 := by
  apply localUnsat_implies_entails f2633 [c2632, c2620, c2544, c5] c2633 unsat2633 (by rfl) a
  have h0 : Entails.eval a c2632 := derived2632 a h
  have h1 : Entails.eval a c2620 := derived2620 a h
  have h2 : Entails.eval a c2544 := derived2544 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2634 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2632, some c2620, some c2624, some c8, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p2634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2634 : lratChecker f2634 p2634 = .success := by decide +kernel
theorem unsat2634 : Unsatisfiable (PosFin 57) f2634 := by
  apply lratCheckerSound f2634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2634
  · intro a ha; simp [p2634] at ha; subst a; trivial
  · exact checked2634
theorem derived2634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2634 := by
  apply localUnsat_implies_entails f2634 [c2632, c2620, c2624, c8] c2634 unsat2634 (by rfl) a
  have h0 : Entails.eval a c2632 := derived2632 a h
  have h1 : Entails.eval a c2620 := derived2620 a h
  have h2 : Entails.eval a c2624 := derived2624 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2635 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2632, some c2620, some c2624, some c2544, some c1031, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p2635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2635 : lratChecker f2635 p2635 = .success := by decide +kernel
theorem unsat2635 : Unsatisfiable (PosFin 57) f2635 := by
  apply lratCheckerSound f2635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2635
  · intro a ha; simp [p2635] at ha; subst a; trivial
  · exact checked2635
theorem derived2635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2635 := by
  apply localUnsat_implies_entails f2635 [c2632, c2620, c2624, c2544, c1031] c2635 unsat2635 (by rfl) a
  have h0 : Entails.eval a c2632 := derived2632 a h
  have h1 : Entails.eval a c2620 := derived2620 a h
  have h2 : Entails.eval a c2624 := derived2624 a h
  have h3 : Entails.eval a c2544 := derived2544 a h
  have h4 : Entails.eval a c1031 := derived1031 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2636 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2634, some c2577, some c2622, some c2600, some c2631, some c1888, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p2636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2636 : lratChecker f2636 p2636 = .success := by decide +kernel
theorem unsat2636 : Unsatisfiable (PosFin 57) f2636 := by
  apply lratCheckerSound f2636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2636
  · intro a ha; simp [p2636] at ha; subst a; trivial
  · exact checked2636
theorem derived2636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2636 := by
  apply localUnsat_implies_entails f2636 [c2634, c2577, c2622, c2600, c2631, c1888] c2636 unsat2636 (by rfl) a
  have h0 : Entails.eval a c2634 := derived2634 a h
  have h1 : Entails.eval a c2577 := derived2577 a h
  have h2 : Entails.eval a c2622 := derived2622 a h
  have h3 : Entails.eval a c2600 := derived2600 a h
  have h4 : Entails.eval a c2631 := derived2631 a h
  have h5 : Entails.eval a c1888 := derived1888 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2637 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2636, some c2635, some c2615, some c209, some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p2637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2637 : lratChecker f2637 p2637 = .success := by decide +kernel
theorem unsat2637 : Unsatisfiable (PosFin 57) f2637 := by
  apply lratCheckerSound f2637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2637
  · intro a ha; simp [p2637] at ha; subst a; trivial
  · exact checked2637
theorem derived2637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2637 := by
  apply localUnsat_implies_entails f2637 [c2636, c2635, c2615, c209] c2637 unsat2637 (by rfl) a
  have h0 : Entails.eval a c2636 := derived2636 a h
  have h1 : Entails.eval a c2635 := derived2635 a h
  have h2 : Entails.eval a c2615 := derived2615 a h
  have h3 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2638 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2636, some c2615, some c2619, some c210, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2638 : lratChecker f2638 p2638 = .success := by decide +kernel
theorem unsat2638 : Unsatisfiable (PosFin 57) f2638 := by
  apply lratCheckerSound f2638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2638
  · intro a ha; simp [p2638] at ha; subst a; trivial
  · exact checked2638
theorem derived2638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2638 := by
  apply localUnsat_implies_entails f2638 [c2636, c2615, c2619, c210] c2638 unsat2638 (by rfl) a
  have h0 : Entails.eval a c2636 := derived2636 a h
  have h1 : Entails.eval a c2615 := derived2615 a h
  have h2 : Entails.eval a c2619 := derived2619 a h
  have h3 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2639 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2637, some c2617, some c2632, some c138, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p2639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2639 : lratChecker f2639 p2639 = .success := by decide +kernel
theorem unsat2639 : Unsatisfiable (PosFin 57) f2639 := by
  apply lratCheckerSound f2639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2639
  · intro a ha; simp [p2639] at ha; subst a; trivial
  · exact checked2639
theorem derived2639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2639 := by
  apply localUnsat_implies_entails f2639 [c2637, c2617, c2632, c138] c2639 unsat2639 (by rfl) a
  have h0 : Entails.eval a c2637 := derived2637 a h
  have h1 : Entails.eval a c2617 := derived2617 a h
  have h2 : Entails.eval a c2632 := derived2632 a h
  have h3 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2640 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2638, some c2544, some c2201, some c27, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p2640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2640 : lratChecker f2640 p2640 = .success := by decide +kernel
theorem unsat2640 : Unsatisfiable (PosFin 57) f2640 := by
  apply lratCheckerSound f2640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2640
  · intro a ha; simp [p2640] at ha; subst a; trivial
  · exact checked2640
theorem derived2640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2640 := by
  apply localUnsat_implies_entails f2640 [c2638, c2544, c2201, c27] c2640 unsat2640 (by rfl) a
  have h0 : Entails.eval a c2638 := derived2638 a h
  have h1 : Entails.eval a c2544 := derived2544 a h
  have h2 : Entails.eval a c2201 := derived2201 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2641 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2639, some c2602, some c2601, some c176, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2641 : lratChecker f2641 p2641 = .success := by decide +kernel
theorem unsat2641 : Unsatisfiable (PosFin 57) f2641 := by
  apply lratCheckerSound f2641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2641
  · intro a ha; simp [p2641] at ha; subst a; trivial
  · exact checked2641
theorem derived2641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2641 := by
  apply localUnsat_implies_entails f2641 [c2639, c2602, c2601, c176] c2641 unsat2641 (by rfl) a
  have h0 : Entails.eval a c2639 := derived2639 a h
  have h1 : Entails.eval a c2602 := derived2602 a h
  have h2 : Entails.eval a c2601 := derived2601 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2642 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2640, some c2613, some c2616, some c2619, some c2630, some c2623, some c2633, some c2627, some c2602, some c2626, some c2603, some c949, some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p2642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2642 : lratChecker f2642 p2642 = .success := by decide +kernel
theorem unsat2642 : Unsatisfiable (PosFin 57) f2642 := by
  apply lratCheckerSound f2642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2642
  · intro a ha; simp [p2642] at ha; subst a; trivial
  · exact checked2642
theorem derived2642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2642 := by
  apply localUnsat_implies_entails f2642 [c2640, c2613, c2616, c2619, c2630, c2623, c2633, c2627, c2602, c2626, c2603, c949] c2642 unsat2642 (by rfl) a
  have h0 : Entails.eval a c2640 := derived2640 a h
  have h1 : Entails.eval a c2613 := derived2613 a h
  have h2 : Entails.eval a c2616 := derived2616 a h
  have h3 : Entails.eval a c2619 := derived2619 a h
  have h4 : Entails.eval a c2630 := derived2630 a h
  have h5 : Entails.eval a c2623 := derived2623 a h
  have h6 : Entails.eval a c2633 := derived2633 a h
  have h7 : Entails.eval a c2627 := derived2627 a h
  have h8 : Entails.eval a c2602 := derived2602 a h
  have h9 : Entails.eval a c2626 := derived2626 a h
  have h10 : Entails.eval a c2603 := derived2603 a h
  have h11 : Entails.eval a c949 := derived949 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2643 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2642, some c2641, some c2613, some c119, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p2643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2643 : lratChecker f2643 p2643 = .success := by decide +kernel
theorem unsat2643 : Unsatisfiable (PosFin 57) f2643 := by
  apply lratCheckerSound f2643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2643
  · intro a ha; simp [p2643] at ha; subst a; trivial
  · exact checked2643
theorem derived2643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2643 := by
  apply localUnsat_implies_entails f2643 [c2642, c2641, c2613, c119] c2643 unsat2643 (by rfl) a
  have h0 : Entails.eval a c2642 := derived2642 a h
  have h1 : Entails.eval a c2641 := derived2641 a h
  have h2 : Entails.eval a c2613 := derived2613 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2644 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2643, some c2628, some c2633, some c158, some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p2644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2644 : lratChecker f2644 p2644 = .success := by decide +kernel
theorem unsat2644 : Unsatisfiable (PosFin 57) f2644 := by
  apply lratCheckerSound f2644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2644
  · intro a ha; simp [p2644] at ha; subst a; trivial
  · exact checked2644
theorem derived2644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2644 := by
  apply localUnsat_implies_entails f2644 [c2643, c2628, c2633, c158] c2644 unsat2644 (by rfl) a
  have h0 : Entails.eval a c2643 := derived2643 a h
  have h1 : Entails.eval a c2628 := derived2628 a h
  have h2 : Entails.eval a c2633 := derived2633 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2645 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f2645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2644, some c2643, some c2636, some c2639, some c2603, some c2633, some c992]
def p2645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2645 : lratChecker f2645 p2645 = .success := by decide +kernel
theorem unsat2645 : Unsatisfiable (PosFin 57) f2645 := by
  apply lratCheckerSound f2645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2645
  · intro a ha; simp [p2645] at ha; subst a; trivial
  · exact checked2645
theorem derived2645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2645 := by
  apply localUnsat_implies_entails f2645 [c2644, c2643, c2636, c2639, c2603, c2633, c992] c2645 unsat2645 (by rfl) a
  have h0 : Entails.eval a c2644 := derived2644 a h
  have h1 : Entails.eval a c2643 := derived2643 a h
  have h2 : Entails.eval a c2636 := derived2636 a h
  have h3 : Entails.eval a c2639 := derived2639 a h
  have h4 : Entails.eval a c2603 := derived2603 a h
  have h5 : Entails.eval a c2633 := derived2633 a h
  have h6 : Entails.eval a c992 := derived992 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2645

end CochromaticTwenty.Certificates.B16_8_2
