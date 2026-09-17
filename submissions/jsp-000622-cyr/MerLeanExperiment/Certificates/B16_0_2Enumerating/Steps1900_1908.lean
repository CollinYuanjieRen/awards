import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1800_1899

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2314 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2311, some c2308, some c110, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2314 : lratChecker f2314 p2314 = .success := by decide +kernel
theorem unsat2314 : Unsatisfiable (PosFin 57) f2314 := by
  apply lratCheckerSound f2314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2314
  · intro a ha; simp [p2314] at ha; subst a; trivial
  · exact checked2314
theorem derived2314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2314 := by
  apply localUnsat_implies_entails f2314 [c2311, c2308, c110] c2314 unsat2314 (by rfl) a
  have h0 : Entails.eval a c2311 := derived2311 a h
  have h1 : Entails.eval a c2308 := derived2308 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2315 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2313, some c2295, some c27, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2315 : lratChecker f2315 p2315 = .success := by decide +kernel
theorem unsat2315 : Unsatisfiable (PosFin 57) f2315 := by
  apply lratCheckerSound f2315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2315
  · intro a ha; simp [p2315] at ha; subst a; trivial
  · exact checked2315
theorem derived2315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2315 := by
  apply localUnsat_implies_entails f2315 [c2313, c2295, c27] c2315 unsat2315 (by rfl) a
  have h0 : Entails.eval a c2313 := derived2313 a h
  have h1 : Entails.eval a c2295 := derived2295 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2316 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2314, some c2312, some c2110, some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p2316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2316 : lratChecker f2316 p2316 = .success := by decide +kernel
theorem unsat2316 : Unsatisfiable (PosFin 57) f2316 := by
  apply lratCheckerSound f2316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2316
  · intro a ha; simp [p2316] at ha; subst a; trivial
  · exact checked2316
theorem derived2316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2316 := by
  apply localUnsat_implies_entails f2316 [c2314, c2312, c2110] c2316 unsat2316 (by rfl) a
  have h0 : Entails.eval a c2314 := derived2314 a h
  have h1 : Entails.eval a c2312 := derived2312 a h
  have h2 : Entails.eval a c2110 := derived2110 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2317 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2316, some c2311, some c2310, some c2308, some c2293, some c2315, some c2294, some c2309, some c2119, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2317 : lratChecker f2317 p2317 = .success := by decide +kernel
theorem unsat2317 : Unsatisfiable (PosFin 57) f2317 := by
  apply lratCheckerSound f2317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2317
  · intro a ha; simp [p2317] at ha; subst a; trivial
  · exact checked2317
theorem derived2317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2317 := by
  apply localUnsat_implies_entails f2317 [c2316, c2311, c2310, c2308, c2293, c2315, c2294, c2309, c2119] c2317 unsat2317 (by rfl) a
  have h0 : Entails.eval a c2316 := derived2316 a h
  have h1 : Entails.eval a c2311 := derived2311 a h
  have h2 : Entails.eval a c2310 := derived2310 a h
  have h3 : Entails.eval a c2308 := derived2308 a h
  have h4 : Entails.eval a c2293 := derived2293 a h
  have h5 : Entails.eval a c2315 := derived2315 a h
  have h6 : Entails.eval a c2294 := derived2294 a h
  have h7 : Entails.eval a c2309 := derived2309 a h
  have h8 : Entails.eval a c2119 := derived2119 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2318 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2317, some c2314, some c2266, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p2318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2318 : lratChecker f2318 p2318 = .success := by decide +kernel
theorem unsat2318 : Unsatisfiable (PosFin 57) f2318 := by
  apply lratCheckerSound f2318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2318
  · intro a ha; simp [p2318] at ha; subst a; trivial
  · exact checked2318
theorem derived2318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2318 := by
  apply localUnsat_implies_entails f2318 [c2317, c2314, c2266] c2318 unsat2318 (by rfl) a
  have h0 : Entails.eval a c2317 := derived2317 a h
  have h1 : Entails.eval a c2314 := derived2314 a h
  have h2 : Entails.eval a c2266 := derived2266 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2319 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2317, some c2310, some c2309, some c2315, some c2293, some c2314, some c2312, some c812, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p2319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2319 : lratChecker f2319 p2319 = .success := by decide +kernel
theorem unsat2319 : Unsatisfiable (PosFin 57) f2319 := by
  apply lratCheckerSound f2319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2319
  · intro a ha; simp [p2319] at ha; subst a; trivial
  · exact checked2319
theorem derived2319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2319 := by
  apply localUnsat_implies_entails f2319 [c2317, c2310, c2309, c2315, c2293, c2314, c2312, c812] c2319 unsat2319 (by rfl) a
  have h0 : Entails.eval a c2317 := derived2317 a h
  have h1 : Entails.eval a c2310 := derived2310 a h
  have h2 : Entails.eval a c2309 := derived2309 a h
  have h3 : Entails.eval a c2315 := derived2315 a h
  have h4 : Entails.eval a c2293 := derived2293 a h
  have h5 : Entails.eval a c2314 := derived2314 a h
  have h6 : Entails.eval a c2312 := derived2312 a h
  have h7 : Entails.eval a c812 := derived812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2320 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2319, some c2311, some c2134, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p2320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2320 : lratChecker f2320 p2320 = .success := by decide +kernel
theorem unsat2320 : Unsatisfiable (PosFin 57) f2320 := by
  apply lratCheckerSound f2320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2320
  · intro a ha; simp [p2320] at ha; subst a; trivial
  · exact checked2320
theorem derived2320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2320 := by
  apply localUnsat_implies_entails f2320 [c2319, c2311, c2134] c2320 unsat2320 (by rfl) a
  have h0 : Entails.eval a c2319 := derived2319 a h
  have h1 : Entails.eval a c2311 := derived2311 a h
  have h2 : Entails.eval a c2134 := derived2134 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2321 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2319, some c2318, some c2308, some c2305, some c2315, some c1236, some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p2321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2321 : lratChecker f2321 p2321 = .success := by decide +kernel
theorem unsat2321 : Unsatisfiable (PosFin 57) f2321 := by
  apply lratCheckerSound f2321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2321
  · intro a ha; simp [p2321] at ha; subst a; trivial
  · exact checked2321
theorem derived2321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2321 := by
  apply localUnsat_implies_entails f2321 [c2319, c2318, c2308, c2305, c2315, c1236] c2321 unsat2321 (by rfl) a
  have h0 : Entails.eval a c2319 := derived2319 a h
  have h1 : Entails.eval a c2318 := derived2318 a h
  have h2 : Entails.eval a c2308 := derived2308 a h
  have h3 : Entails.eval a c2305 := derived2305 a h
  have h4 : Entails.eval a c2315 := derived2315 a h
  have h5 : Entails.eval a c1236 := derived1236 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2322 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f2322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2321, some c2320, some c2292, some c2295, some c216]
def p2322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2322 : lratChecker f2322 p2322 = .success := by decide +kernel
theorem unsat2322 : Unsatisfiable (PosFin 57) f2322 := by
  apply lratCheckerSound f2322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2322
  · intro a ha; simp [p2322] at ha; subst a; trivial
  · exact checked2322
theorem derived2322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2322 := by
  apply localUnsat_implies_entails f2322 [c2321, c2320, c2292, c2295, c216] c2322 unsat2322 (by rfl) a
  have h0 : Entails.eval a c2321 := derived2321 a h
  have h1 : Entails.eval a c2320 := derived2320 a h
  have h2 : Entails.eval a c2292 := derived2292 a h
  have h3 : Entails.eval a c2295 := derived2295 a h
  have h4 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2322

end CochromaticTwenty.Certificates.B16_0_2Enumerating
