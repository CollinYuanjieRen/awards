import MerLeanExperiment.Certificates.B16_8_2.Steps1600_1699

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2081 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c369, some c368, some c2017, some c71, some c841, some c84, some c1241, some c162, some c154, some c359, some c380, some c156, some c983, some c2080, some c1981, some c2005, some c1085, some c9, some c2076, some c171, some c2052, some c333, some c335, some c2001, some c266, some c2067, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2081 : lratChecker f2081 p2081 = .success := by decide +kernel
theorem unsat2081 : Unsatisfiable (PosFin 57) f2081 := by
  apply lratCheckerSound f2081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2081
  · intro a ha; simp [p2081] at ha; subst a; trivial
  · exact checked2081
theorem derived2081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2081 := by
  apply localUnsat_implies_entails f2081 [c77, c369, c368, c2017, c71, c841, c84, c1241, c162, c154, c359, c380, c156, c983, c2080, c1981, c2005, c1085, c9, c2076, c171, c2052, c333, c335, c2001, c266, c2067] c2081 unsat2081 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c2017 := derived2017 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1241 := derived1241 a h
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c156 := h 155 (by decide)
  have h13 : Entails.eval a c983 := derived983 a h
  have h14 : Entails.eval a c2080 := derived2080 a h
  have h15 : Entails.eval a c1981 := derived1981 a h
  have h16 : Entails.eval a c2005 := derived2005 a h
  have h17 : Entails.eval a c1085 := derived1085 a h
  have h18 : Entails.eval a c9 := h 8 (by decide)
  have h19 : Entails.eval a c2076 := derived2076 a h
  have h20 : Entails.eval a c171 := h 170 (by decide)
  have h21 : Entails.eval a c2052 := derived2052 a h
  have h22 : Entails.eval a c333 := h 332 (by decide)
  have h23 : Entails.eval a c335 := h 334 (by decide)
  have h24 : Entails.eval a c2001 := derived2001 a h
  have h25 : Entails.eval a c266 := h 265 (by decide)
  have h26 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2082 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2080, some c77, some c2017, some c71, some c841, some c368, some c359, some c2081, some c2007, some c968, some c103, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2082 : lratChecker f2082 p2082 = .success := by decide +kernel
theorem unsat2082 : Unsatisfiable (PosFin 57) f2082 := by
  apply lratCheckerSound f2082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2082
  · intro a ha; simp [p2082] at ha; subst a; trivial
  · exact checked2082
theorem derived2082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2082 := by
  apply localUnsat_implies_entails f2082 [c2080, c77, c2017, c71, c841, c368, c359, c2081, c2007, c968, c103] c2082 unsat2082 (by rfl) a
  have h0 : Entails.eval a c2080 := derived2080 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c2017 := derived2017 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c2081 := derived2081 a h
  have h8 : Entails.eval a c2007 := derived2007 a h
  have h9 : Entails.eval a c968 := derived968 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2083 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2017, some c71, some c841, some c84, some c154, some c1241, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2083 : lratChecker f2083 p2083 = .success := by decide +kernel
theorem unsat2083 : Unsatisfiable (PosFin 57) f2083 := by
  apply lratCheckerSound f2083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2083
  · intro a ha; simp [p2083] at ha; subst a; trivial
  · exact checked2083
theorem derived2083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2083 := by
  apply localUnsat_implies_entails f2083 [c2017, c71, c841, c84, c154, c1241] c2083 unsat2083 (by rfl) a
  have h0 : Entails.eval a c2017 := derived2017 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c1241 := derived1241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2084 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨46, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨5, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c143, some c56, some c266, some c319, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2084 : lratChecker f2084 p2084 = .success := by decide +kernel
theorem unsat2084 : Unsatisfiable (PosFin 57) f2084 := by
  apply lratCheckerSound f2084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2084
  · intro a ha; simp [p2084] at ha; subst a; trivial
  · exact checked2084
theorem derived2084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2084 := by
  apply localUnsat_implies_entails f2084 [c342, c143, c56, c266, c319] c2084 unsat2084 (by rfl) a
  have h0 : Entails.eval a c342 := h 341 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2085 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2017, some c71, some c841, some c2082, some c361, some c2080, some c80, some c103, some c2008, some c377, some c2083, some c968, some c1118, some c9, some c164, some c359, some c77, some c156, some c1981, some c597, some c277, some c279, some c2084, some c57, some c39, some c317, some c132, some c267, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2085 : lratChecker f2085 p2085 = .success := by decide +kernel
theorem unsat2085 : Unsatisfiable (PosFin 57) f2085 := by
  apply lratCheckerSound f2085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2085
  · intro a ha; simp [p2085] at ha; subst a; trivial
  · exact checked2085
theorem derived2085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2085 := by
  apply localUnsat_implies_entails f2085 [c2017, c71, c841, c2082, c361, c2080, c80, c103, c2008, c377, c2083, c968, c1118, c9, c164, c359, c77, c156, c1981, c597, c277, c279, c2084, c57, c39, c317, c132, c267] c2085 unsat2085 (by rfl) a
  have h0 : Entails.eval a c2017 := derived2017 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c2082 := derived2082 a h
  have h4 : Entails.eval a c361 := h 360 (by decide)
  have h5 : Entails.eval a c2080 := derived2080 a h
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c2008 := derived2008 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c2083 := derived2083 a h
  have h11 : Entails.eval a c968 := derived968 a h
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c164 := h 163 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c1981 := derived1981 a h
  have h19 : Entails.eval a c597 := derived597 a h
  have h20 : Entails.eval a c277 := h 276 (by decide)
  have h21 : Entails.eval a c279 := h 278 (by decide)
  have h22 : Entails.eval a c2084 := derived2084 a h
  have h23 : Entails.eval a c57 := h 56 (by decide)
  have h24 : Entails.eval a c39 := h 38 (by decide)
  have h25 : Entails.eval a c317 := h 316 (by decide)
  have h26 : Entails.eval a c132 := h 131 (by decide)
  have h27 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2086 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2017, some c71, some c841, some c2080, some c2082, some c80, some c361, some c103, some c968, some c2008, some c1118, some c377, some c1491, some c2085, some c94, some c178, some c1241, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2086 : lratChecker f2086 p2086 = .success := by decide +kernel
theorem unsat2086 : Unsatisfiable (PosFin 57) f2086 := by
  apply lratCheckerSound f2086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2086
  · intro a ha; simp [p2086] at ha; subst a; trivial
  · exact checked2086
theorem derived2086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2086 := by
  apply localUnsat_implies_entails f2086 [c2017, c71, c841, c2080, c2082, c80, c361, c103, c968, c2008, c1118, c377, c1491, c2085, c94, c178, c1241] c2086 unsat2086 (by rfl) a
  have h0 : Entails.eval a c2017 := derived2017 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c2080 := derived2080 a h
  have h4 : Entails.eval a c2082 := derived2082 a h
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c361 := h 360 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c968 := derived968 a h
  have h9 : Entails.eval a c2008 := derived2008 a h
  have h10 : Entails.eval a c1118 := derived1118 a h
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c1491 := derived1491 a h
  have h13 : Entails.eval a c2085 := derived2085 a h
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c1241 := derived1241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2087 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨31, by decide⟩, false), (⟨39, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c331, some c291, some c2025, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2087 : lratChecker f2087 p2087 = .success := by decide +kernel
theorem unsat2087 : Unsatisfiable (PosFin 57) f2087 := by
  apply lratCheckerSound f2087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2087
  · intro a ha; simp [p2087] at ha; subst a; trivial
  · exact checked2087
theorem derived2087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2087 := by
  apply localUnsat_implies_entails f2087 [c331, c291, c2025] c2087 unsat2087 (by rfl) a
  have h0 : Entails.eval a c331 := h 330 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c2025 := derived2025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2088 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c2017, some c72, some c2086, some c102, some c84, some c156, some c8, some c369, some c1142, some c161, some c183, some c1668, some c100, some c946, some c1461, some c2087, some c2037, some c376, some c1118, some c359, some c188, some c1245, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2088 : lratChecker f2088 p2088 = .success := by decide +kernel
theorem unsat2088 : Unsatisfiable (PosFin 57) f2088 := by
  apply lratCheckerSound f2088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2088
  · intro a ha; simp [p2088] at ha; subst a; trivial
  · exact checked2088
theorem derived2088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2088 := by
  apply localUnsat_implies_entails f2088 [c71, c841, c2017, c72, c2086, c102, c84, c156, c8, c369, c1142, c161, c183, c1668, c100, c946, c1461, c2087, c2037, c376, c1118, c359, c188, c1245] c2088 unsat2088 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c2017 := derived2017 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c2086 := derived2086 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c1142 := derived1142 a h
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c1668 := derived1668 a h
  have h14 : Entails.eval a c100 := h 99 (by decide)
  have h15 : Entails.eval a c946 := derived946 a h
  have h16 : Entails.eval a c1461 := derived1461 a h
  have h17 : Entails.eval a c2087 := derived2087 a h
  have h18 : Entails.eval a c2037 := derived2037 a h
  have h19 : Entails.eval a c376 := h 375 (by decide)
  have h20 : Entails.eval a c1118 := derived1118 a h
  have h21 : Entails.eval a c359 := h 358 (by decide)
  have h22 : Entails.eval a c188 := h 187 (by decide)
  have h23 : Entails.eval a c1245 := derived1245 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2089 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨38, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2027, some c2055, some c2062, some c2025, some c2026, some c46, some c917, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p2089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2089 : lratChecker f2089 p2089 = .success := by decide +kernel
theorem unsat2089 : Unsatisfiable (PosFin 57) f2089 := by
  apply lratCheckerSound f2089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2089
  · intro a ha; simp [p2089] at ha; subst a; trivial
  · exact checked2089
theorem derived2089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2089 := by
  apply localUnsat_implies_entails f2089 [c2027, c2055, c2062, c2025, c2026, c46, c917] c2089 unsat2089 (by rfl) a
  have h0 : Entails.eval a c2027 := derived2027 a h
  have h1 : Entails.eval a c2055 := derived2055 a h
  have h2 : Entails.eval a c2062 := derived2062 a h
  have h3 : Entails.eval a c2025 := derived2025 a h
  have h4 : Entails.eval a c2026 := derived2026 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c917 := derived917 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2090 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2086, some c2088, some c80, some c100, some c2017, some c71, some c841, some c361, some c72, some c102, some c156, some c183, some c1667, some c1670, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2090 : lratChecker f2090 p2090 = .success := by decide +kernel
theorem unsat2090 : Unsatisfiable (PosFin 57) f2090 := by
  apply lratCheckerSound f2090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2090
  · intro a ha; simp [p2090] at ha; subst a; trivial
  · exact checked2090
theorem derived2090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2090 := by
  apply localUnsat_implies_entails f2090 [c2086, c2088, c80, c100, c2017, c71, c841, c361, c72, c102, c156, c183, c1667, c1670] c2090 unsat2090 (by rfl) a
  have h0 : Entails.eval a c2086 := derived2086 a h
  have h1 : Entails.eval a c2088 := derived2088 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c2017 := derived2017 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c1667 := derived1667 a h
  have h13 : Entails.eval a c1670 := derived1670 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2091 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2088, some c2090, some c164, some c2086, some c80, some c100, some c2017, some c71, some c841, some c361, some c72, some c102, some c84, some c156, some c8, some c380, some c376, some c1632, some c363, some c1965, some c150, some c2089, some c12, some c596, some c1641, some c2021, some c2062, some c2035, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2091 : lratChecker f2091 p2091 = .success := by decide +kernel
theorem unsat2091 : Unsatisfiable (PosFin 57) f2091 := by
  apply lratCheckerSound f2091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2091
  · intro a ha; simp [p2091] at ha; subst a; trivial
  · exact checked2091
theorem derived2091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2091 := by
  apply localUnsat_implies_entails f2091 [c2088, c2090, c164, c2086, c80, c100, c2017, c71, c841, c361, c72, c102, c84, c156, c8, c380, c376, c1632, c363, c1965, c150, c2089, c12, c596, c1641, c2021, c2062, c2035] c2091 unsat2091 (by rfl) a
  have h0 : Entails.eval a c2088 := derived2088 a h
  have h1 : Entails.eval a c2090 := derived2090 a h
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c2086 := derived2086 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c2017 := derived2017 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c376 := h 375 (by decide)
  have h17 : Entails.eval a c1632 := derived1632 a h
  have h18 : Entails.eval a c363 := h 362 (by decide)
  have h19 : Entails.eval a c1965 := derived1965 a h
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c2089 := derived2089 a h
  have h22 : Entails.eval a c12 := h 11 (by decide)
  have h23 : Entails.eval a c596 := derived596 a h
  have h24 : Entails.eval a c1641 := derived1641 a h
  have h25 : Entails.eval a c2021 := derived2021 a h
  have h26 : Entails.eval a c2062 := derived2062 a h
  have h27 : Entails.eval a c2035 := derived2035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2092 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c841, some c2017, some c72, some c156, some c2086, some c2088, some c80, some c361, some c100, some c2091, some c1118, some c2036, some c1491, some c373, some c1965, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2092 : lratChecker f2092 p2092 = .success := by decide +kernel
theorem unsat2092 : Unsatisfiable (PosFin 57) f2092 := by
  apply lratCheckerSound f2092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2092
  · intro a ha; simp [p2092] at ha; subst a; trivial
  · exact checked2092
theorem derived2092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2092 := by
  apply localUnsat_implies_entails f2092 [c71, c841, c2017, c72, c156, c2086, c2088, c80, c361, c100, c2091, c1118, c2036, c1491, c373, c1965] c2092 unsat2092 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c2017 := derived2017 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c2086 := derived2086 a h
  have h6 : Entails.eval a c2088 := derived2088 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c2091 := derived2091 a h
  have h11 : Entails.eval a c1118 := derived1118 a h
  have h12 : Entails.eval a c2036 := derived2036 a h
  have h13 : Entails.eval a c1491 := derived1491 a h
  have h14 : Entails.eval a c373 := h 372 (by decide)
  have h15 : Entails.eval a c1965 := derived1965 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2093 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c2027, some c368, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2093 : lratChecker f2093 p2093 = .success := by decide +kernel
theorem unsat2093 : Unsatisfiable (PosFin 57) f2093 := by
  apply lratCheckerSound f2093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2093
  · intro a ha; simp [p2093] at ha; subst a; trivial
  · exact checked2093
theorem derived2093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2093 := by
  apply localUnsat_implies_entails f2093 [c2068, c2027, c368] c2093 unsat2093 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c2027 := derived2027 a h
  have h2 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2094 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c363, some c380, some c373, some c2036, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2094 : lratChecker f2094 p2094 = .success := by decide +kernel
theorem unsat2094 : Unsatisfiable (PosFin 57) f2094 := by
  apply lratCheckerSound f2094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2094
  · intro a ha; simp [p2094] at ha; subst a; trivial
  · exact checked2094
theorem derived2094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2094 := by
  apply localUnsat_implies_entails f2094 [c841, c363, c380, c373, c2036] c2094 unsat2094 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c2036 := derived2036 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2095 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨14, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c368, some c166, some c162, some c1480, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2095 : lratChecker f2095 p2095 = .success := by decide +kernel
theorem unsat2095 : Unsatisfiable (PosFin 57) f2095 := by
  apply lratCheckerSound f2095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2095
  · intro a ha; simp [p2095] at ha; subst a; trivial
  · exact checked2095
theorem derived2095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2095 := by
  apply localUnsat_implies_entails f2095 [c369, c368, c166, c162, c1480] c2095 unsat2095 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c1480 := derived1480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2096 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c365, some c367, some c363, some c156, some c2094, some c154, some c166, some c1480, some c12, some c162, some c176, some c183, some c171, some c992, some c223, some c1003, some c2071, some c2025, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2096 : lratChecker f2096 p2096 = .success := by decide +kernel
theorem unsat2096 : Unsatisfiable (PosFin 57) f2096 := by
  apply lratCheckerSound f2096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2096
  · intro a ha; simp [p2096] at ha; subst a; trivial
  · exact checked2096
theorem derived2096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2096 := by
  apply localUnsat_implies_entails f2096 [c365, c367, c363, c156, c2094, c154, c166, c1480, c12, c162, c176, c183, c171, c992, c223, c1003, c2071, c2025] c2096 unsat2096 (by rfl) a
  have h0 : Entails.eval a c365 := h 364 (by decide)
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c1480 := derived1480 a h
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c171 := h 170 (by decide)
  have h13 : Entails.eval a c992 := derived992 a h
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c1003 := derived1003 a h
  have h16 : Entails.eval a c2071 := derived2071 a h
  have h17 : Entails.eval a c2025 := derived2025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2097 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2050, some c2026, some c333, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2097 : lratChecker f2097 p2097 = .success := by decide +kernel
theorem unsat2097 : Unsatisfiable (PosFin 57) f2097 := by
  apply lratCheckerSound f2097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2097
  · intro a ha; simp [p2097] at ha; subst a; trivial
  · exact checked2097
theorem derived2097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2097 := by
  apply localUnsat_implies_entails f2097 [c2050, c2026, c333] c2097 unsat2097 (by rfl) a
  have h0 : Entails.eval a c2050 := derived2050 a h
  have h1 : Entails.eval a c2026 := derived2026 a h
  have h2 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2098 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c367, some c365, some c2094, some c89, some c2097, some c315, some c57, some c39, some c333, some c275, some c35, some c2061, some c293, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2098 : lratChecker f2098 p2098 = .success := by decide +kernel
theorem unsat2098 : Unsatisfiable (PosFin 57) f2098 := by
  apply lratCheckerSound f2098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2098
  · intro a ha; simp [p2098] at ha; subst a; trivial
  · exact checked2098
theorem derived2098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2098 := by
  apply localUnsat_implies_entails f2098 [c2092, c367, c365, c2094, c89, c2097, c315, c57, c39, c333, c275, c35, c2061, c293] c2098 unsat2098 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c2097 := derived2097 a h
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c275 := h 274 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c2061 := derived2061 a h
  have h13 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2099 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c67, some c367, some c1205, some c992, some c2074, some c223, some c2071, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2099 : lratChecker f2099 p2099 = .success := by decide +kernel
theorem unsat2099 : Unsatisfiable (PosFin 57) f2099 := by
  apply lratCheckerSound f2099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2099
  · intro a ha; simp [p2099] at ha; subst a; trivial
  · exact checked2099
theorem derived2099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2099 := by
  apply localUnsat_implies_entails f2099 [c67, c367, c1205, c992, c2074, c223, c2071] c2099 unsat2099 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c992 := derived992 a h
  have h4 : Entails.eval a c2074 := derived2074 a h
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c2071 := derived2071 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2100 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c323, some c2026, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2100 : lratChecker f2100 p2100 = .success := by decide +kernel
theorem unsat2100 : Unsatisfiable (PosFin 57) f2100 := by
  apply lratCheckerSound f2100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2100
  · intro a ha; simp [p2100] at ha; subst a; trivial
  · exact checked2100
theorem derived2100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2100 := by
  apply localUnsat_implies_entails f2100 [c315, c323, c2026] c2100 unsat2100 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c2026 := derived2026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2101 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2098, some c67, some c2100, some c39, some c275, some c283, some c2047, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2101 : lratChecker f2101 p2101 = .success := by decide +kernel
theorem unsat2101 : Unsatisfiable (PosFin 57) f2101 := by
  apply lratCheckerSound f2101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2101
  · intro a ha; simp [p2101] at ha; subst a; trivial
  · exact checked2101
theorem derived2101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2101 := by
  apply localUnsat_implies_entails f2101 [c2092, c2098, c67, c2100, c39, c275, c283, c2047] c2101 unsat2101 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2098 := derived2098 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c2100 := derived2100 a h
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c275 := h 274 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c2047 := derived2047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2102 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2101, some c2027, some c2068, some c2092, some c57, some c39, some c317, some c283, some c35, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2102 : lratChecker f2102 p2102 = .success := by decide +kernel
theorem unsat2102 : Unsatisfiable (PosFin 57) f2102 := by
  apply lratCheckerSound f2102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2102
  · intro a ha; simp [p2102] at ha; subst a; trivial
  · exact checked2102
theorem derived2102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2102 := by
  apply localUnsat_implies_entails f2102 [c2101, c2027, c2068, c2092, c57, c39, c317, c283, c35] c2102 unsat2102 (by rfl) a
  have h0 : Entails.eval a c2101 := derived2101 a h
  have h1 : Entails.eval a c2027 := derived2027 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2103 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2101, some c2068, some c2027, some c2102, some c323, some c35, some c283, some c277, some c45, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2103 : lratChecker f2103 p2103 = .success := by decide +kernel
theorem unsat2103 : Unsatisfiable (PosFin 57) f2103 := by
  apply lratCheckerSound f2103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2103
  · intro a ha; simp [p2103] at ha; subst a; trivial
  · exact checked2103
theorem derived2103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2103 := by
  apply localUnsat_implies_entails f2103 [c2092, c2101, c2068, c2027, c2102, c323, c35, c283, c277, c45] c2103 unsat2103 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2101 := derived2101 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c2027 := derived2027 a h
  have h4 : Entails.eval a c2102 := derived2102 a h
  have h5 : Entails.eval a c323 := h 322 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2104 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c367, some c2068, some c2002, some c2035, some c2052, some c320, some c318, some c269, some c278, some c2061, some c45, some c291, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2104 : lratChecker f2104 p2104 = .success := by decide +kernel
theorem unsat2104 : Unsatisfiable (PosFin 57) f2104 := by
  apply lratCheckerSound f2104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2104
  · intro a ha; simp [p2104] at ha; subst a; trivial
  · exact checked2104
theorem derived2104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2104 := by
  apply localUnsat_implies_entails f2104 [c2092, c367, c2068, c2002, c2035, c2052, c320, c318, c269, c278, c2061, c45, c291] c2104 unsat2104 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c2002 := derived2002 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2052 := derived2052 a h
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c2061 := derived2061 a h
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2105 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c2092, some c367, some c2068, some c2002, some c2103, some c328, some c2001, some c333, some c352, some c56, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2105 : lratChecker f2105 p2105 = .success := by decide +kernel
theorem unsat2105 : Unsatisfiable (PosFin 57) f2105 := by
  apply lratCheckerSound f2105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2105
  · intro a ha; simp [p2105] at ha; subst a; trivial
  · exact checked2105
theorem derived2105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2105 := by
  apply localUnsat_implies_entails f2105 [c376, c2092, c367, c2068, c2002, c2103, c328, c2001, c333, c352, c56] c2105 unsat2105 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2068 := derived2068 a h
  have h4 : Entails.eval a c2002 := derived2002 a h
  have h5 : Entails.eval a c2103 := derived2103 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c2001 := derived2001 a h
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2106 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c2092, some c367, some c2068, some c2002, some c2103, some c376, some c92, some c103, some c2105, some c57, some c320, some c333, some c2001, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2106 : lratChecker f2106 p2106 = .success := by decide +kernel
theorem unsat2106 : Unsatisfiable (PosFin 57) f2106 := by
  apply lratCheckerSound f2106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2106
  · intro a ha; simp [p2106] at ha; subst a; trivial
  · exact checked2106
theorem derived2106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2106 := by
  apply localUnsat_implies_entails f2106 [c89, c2092, c367, c2068, c2002, c2103, c376, c92, c103, c2105, c57, c320, c333, c2001] c2106 unsat2106 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2068 := derived2068 a h
  have h4 : Entails.eval a c2002 := derived2002 a h
  have h5 : Entails.eval a c2103 := derived2103 a h
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c2105 := derived2105 a h
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c2001 := derived2001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2107 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨32, by decide⟩, true), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c2068, some c2035, some c328, some c143, some c196, some c267, some c236, some c228, some c127, some c2054, some c121, some c295, some c105, some c208, some c238, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2107 : lratChecker f2107 p2107 = .success := by decide +kernel
theorem unsat2107 : Unsatisfiable (PosFin 57) f2107 := by
  apply lratCheckerSound f2107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2107
  · intro a ha; simp [p2107] at ha; subst a; trivial
  · exact checked2107
theorem derived2107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2107 := by
  apply localUnsat_implies_entails f2107 [c367, c2068, c2035, c328, c143, c196, c267, c236, c228, c127, c2054, c121, c295, c105, c208, c238] c2107 unsat2107 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c2054 := derived2054 a h
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2108 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2103, some c2092, some c367, some c2068, some c369, some c368, some c2002, some c2104, some c89, some c2106, some c358, some c151, some c1700, some c377, some c92, some c103, some c9, some c176, some c177, some c183, some c2107, some c57, some c39, some c320, some c318, some c2058, some c269, some c305, some c278, some c44, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2108 : lratChecker f2108 p2108 = .success := by decide +kernel
theorem unsat2108 : Unsatisfiable (PosFin 57) f2108 := by
  apply lratCheckerSound f2108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2108
  · intro a ha; simp [p2108] at ha; subst a; trivial
  · exact checked2108
theorem derived2108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2108 := by
  apply localUnsat_implies_entails f2108 [c2103, c2092, c367, c2068, c369, c368, c2002, c2104, c89, c2106, c358, c151, c1700, c377, c92, c103, c9, c176, c177, c183, c2107, c57, c39, c320, c318, c2058, c269, c305, c278, c44] c2108 unsat2108 (by rfl) a
  have h0 : Entails.eval a c2103 := derived2103 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2068 := derived2068 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c2002 := derived2002 a h
  have h7 : Entails.eval a c2104 := derived2104 a h
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c2106 := derived2106 a h
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c151 := h 150 (by decide)
  have h12 : Entails.eval a c1700 := derived1700 a h
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c176 := h 175 (by decide)
  have h18 : Entails.eval a c177 := h 176 (by decide)
  have h19 : Entails.eval a c183 := h 182 (by decide)
  have h20 : Entails.eval a c2107 := derived2107 a h
  have h21 : Entails.eval a c57 := h 56 (by decide)
  have h22 : Entails.eval a c39 := h 38 (by decide)
  have h23 : Entails.eval a c320 := h 319 (by decide)
  have h24 : Entails.eval a c318 := h 317 (by decide)
  have h25 : Entails.eval a c2058 := derived2058 a h
  have h26 : Entails.eval a c269 := h 268 (by decide)
  have h27 : Entails.eval a c305 := h 304 (by decide)
  have h28 : Entails.eval a c278 := h 277 (by decide)
  have h29 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2109 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c841, some c2108, some c380, some c363, some c365, some c2068, some c2035, some c2052, some c318, some c2103, some c103, some c1085, some c2076, some c333, some c191, some c25, some c247, some c241, some c192, some c2054, some c278, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2109 : lratChecker f2109 p2109 = .success := by decide +kernel
theorem unsat2109 : Unsatisfiable (PosFin 57) f2109 := by
  apply lratCheckerSound f2109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2109
  · intro a ha; simp [p2109] at ha; subst a; trivial
  · exact checked2109
theorem derived2109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2109 := by
  apply localUnsat_implies_entails f2109 [c2092, c841, c2108, c380, c363, c365, c2068, c2035, c2052, c318, c2103, c103, c1085, c2076, c333, c191, c25, c247, c241, c192, c2054, c278] c2109 unsat2109 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c2108 := derived2108 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c2068 := derived2068 a h
  have h7 : Entails.eval a c2035 := derived2035 a h
  have h8 : Entails.eval a c2052 := derived2052 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c2103 := derived2103 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c1085 := derived1085 a h
  have h13 : Entails.eval a c2076 := derived2076 a h
  have h14 : Entails.eval a c333 := h 332 (by decide)
  have h15 : Entails.eval a c191 := h 190 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c247 := h 246 (by decide)
  have h18 : Entails.eval a c241 := h 240 (by decide)
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c2054 := derived2054 a h
  have h21 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2110 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2108, some c2092, some c841, some c380, some c363, some c365, some c2035, some c2068, some c2052, some c318, some c2109, some c60, some c2033, some c331, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2110 : lratChecker f2110 p2110 = .success := by decide +kernel
theorem unsat2110 : Unsatisfiable (PosFin 57) f2110 := by
  apply lratCheckerSound f2110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2110
  · intro a ha; simp [p2110] at ha; subst a; trivial
  · exact checked2110
theorem derived2110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2110 := by
  apply localUnsat_implies_entails f2110 [c2108, c2092, c841, c380, c363, c365, c2035, c2068, c2052, c318, c2109, c60, c2033, c331] c2110 unsat2110 (by rfl) a
  have h0 : Entails.eval a c2108 := derived2108 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c2068 := derived2068 a h
  have h8 : Entails.eval a c2052 := derived2052 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c2109 := derived2109 a h
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c2033 := derived2033 a h
  have h13 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2111 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨43, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c365, some c1414, some c82, some c2095, some c13, some c15, some c176, some c163, some c167, some c188, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2111 : lratChecker f2111 p2111 = .success := by decide +kernel
theorem unsat2111 : Unsatisfiable (PosFin 57) f2111 := by
  apply lratCheckerSound f2111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2111
  · intro a ha; simp [p2111] at ha; subst a; trivial
  · exact checked2111
theorem derived2111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2111 := by
  apply localUnsat_implies_entails f2111 [c369, c365, c1414, c82, c2095, c13, c15, c176, c163, c167, c188] c2111 unsat2111 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c1414 := derived1414 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c2095 := derived2095 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2112 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c158, some c182, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p2112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2112 : lratChecker f2112 p2112 = .success := by decide +kernel
theorem unsat2112 : Unsatisfiable (PosFin 57) f2112 := by
  apply lratCheckerSound f2112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2112
  · intro a ha; simp [p2112] at ha; subst a; trivial
  · exact checked2112
theorem derived2112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2112 := by
  apply localUnsat_implies_entails f2112 [c162, c158, c182] c2112 unsat2112 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2113 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2108, some c156, some c2110, some c89, some c376, some c92, some c2103, some c103, some c976, some c369, some c2092, some c2111, some c2112, some c9, some c176, some c148, some c2001, some c2067, some c132, some c52, some c45, some c1241, some c293, some c2095, some c154, some c266, some c326, some c335, some c56, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked2113 : lratChecker f2113 p2113 = .success := by decide +kernel
theorem unsat2113 : Unsatisfiable (PosFin 57) f2113 := by
  apply lratCheckerSound f2113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2113
  · intro a ha; simp [p2113] at ha; subst a; trivial
  · exact checked2113
theorem derived2113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2113 := by
  apply localUnsat_implies_entails f2113 [c2108, c156, c2110, c89, c376, c92, c2103, c103, c976, c369, c2092, c2111, c2112, c9, c176, c148, c2001, c2067, c132, c52, c45, c1241, c293, c2095, c154, c266, c326, c335, c56] c2113 unsat2113 (by rfl) a
  have h0 : Entails.eval a c2108 := derived2108 a h
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c2110 := derived2110 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c2103 := derived2103 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c976 := derived976 a h
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c2092 := derived2092 a h
  have h11 : Entails.eval a c2111 := derived2111 a h
  have h12 : Entails.eval a c2112 := derived2112 a h
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c2001 := derived2001 a h
  have h17 : Entails.eval a c2067 := derived2067 a h
  have h18 : Entails.eval a c132 := h 131 (by decide)
  have h19 : Entails.eval a c52 := h 51 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c1241 := derived1241 a h
  have h22 : Entails.eval a c293 := h 292 (by decide)
  have h23 : Entails.eval a c2095 := derived2095 a h
  have h24 : Entails.eval a c154 := h 153 (by decide)
  have h25 : Entails.eval a c266 := h 265 (by decide)
  have h26 : Entails.eval a c326 := h 325 (by decide)
  have h27 : Entails.eval a c335 := h 334 (by decide)
  have h28 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2114 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2108, some c2110, some c89, some c376, some c92, some c2103, some c103, some c976, some c2111, some c369, some c156, some c2112, some c9, some c176, some c2113, some c143, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2114 : lratChecker f2114 p2114 = .success := by decide +kernel
theorem unsat2114 : Unsatisfiable (PosFin 57) f2114 := by
  apply lratCheckerSound f2114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2114
  · intro a ha; simp [p2114] at ha; subst a; trivial
  · exact checked2114
theorem derived2114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2114 := by
  apply localUnsat_implies_entails f2114 [c2092, c2108, c2110, c89, c376, c92, c2103, c103, c976, c2111, c369, c156, c2112, c9, c176, c2113, c143] c2114 unsat2114 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2108 := derived2108 a h
  have h2 : Entails.eval a c2110 := derived2110 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c2103 := derived2103 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c976 := derived976 a h
  have h9 : Entails.eval a c2111 := derived2111 a h
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c2112 := derived2112 a h
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c2113 := derived2113 a h
  have h16 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2115 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨41, by decide⟩, true), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c2112, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p2115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2115 : lratChecker f2115 p2115 = .success := by decide +kernel
theorem unsat2115 : Unsatisfiable (PosFin 57) f2115 := by
  apply lratCheckerSound f2115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2115
  · intro a ha; simp [p2115] at ha; subst a; trivial
  · exact checked2115
theorem derived2115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2115 := by
  apply localUnsat_implies_entails f2115 [c163, c2112] c2115 unsat2115 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c2112 := derived2112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2116 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2114, some c2103, some c2110, some c89, some c376, some c92, some c103, some c2092, some c326, some c37, some c56, some c286, some c284, some c336, some c318, some c45, some c269, some c296, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2116 : lratChecker f2116 p2116 = .success := by decide +kernel
theorem unsat2116 : Unsatisfiable (PosFin 57) f2116 := by
  apply lratCheckerSound f2116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2116
  · intro a ha; simp [p2116] at ha; subst a; trivial
  · exact checked2116
theorem derived2116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2116 := by
  apply localUnsat_implies_entails f2116 [c2114, c2103, c2110, c89, c376, c92, c103, c2092, c326, c37, c56, c286, c284, c336, c318, c45, c269, c296] c2116 unsat2116 (by rfl) a
  have h0 : Entails.eval a c2114 := derived2114 a h
  have h1 : Entails.eval a c2103 := derived2103 a h
  have h2 : Entails.eval a c2110 := derived2110 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c2092 := derived2092 a h
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2117 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2110, some c89, some c376, some c2108, some c2103, some c92, some c103, some c976, some c369, some c2092, some c2111, some c2115, some c1480, some c2114, some c1700, some c96, some c154, some c2116, some c83, some c167, some c15, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2117 : lratChecker f2117 p2117 = .success := by decide +kernel
theorem unsat2117 : Unsatisfiable (PosFin 57) f2117 := by
  apply lratCheckerSound f2117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2117
  · intro a ha; simp [p2117] at ha; subst a; trivial
  · exact checked2117
theorem derived2117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2117 := by
  apply localUnsat_implies_entails f2117 [c2110, c89, c376, c2108, c2103, c92, c103, c976, c369, c2092, c2111, c2115, c1480, c2114, c1700, c96, c154, c2116, c83, c167, c15] c2117 unsat2117 (by rfl) a
  have h0 : Entails.eval a c2110 := derived2110 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c2108 := derived2108 a h
  have h4 : Entails.eval a c2103 := derived2103 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c976 := derived976 a h
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c2092 := derived2092 a h
  have h10 : Entails.eval a c2111 := derived2111 a h
  have h11 : Entails.eval a c2115 := derived2115 a h
  have h12 : Entails.eval a c1480 := derived1480 a h
  have h13 : Entails.eval a c2114 := derived2114 a h
  have h14 : Entails.eval a c1700 := derived1700 a h
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c154 := h 153 (by decide)
  have h17 : Entails.eval a c2116 := derived2116 a h
  have h18 : Entails.eval a c83 := h 82 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2118 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2103, some c2110, some c89, some c376, some c92, some c103, some c976, some c2108, some c2092, some c369, some c2111, some c2115, some c2117, some c9, some c57, some c39, some c176, some c318, some c333, some c127, some c191, some c25, some c192, some c278, some c2061, some c44, some c305, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked2118 : lratChecker f2118 p2118 = .success := by decide +kernel
theorem unsat2118 : Unsatisfiable (PosFin 57) f2118 := by
  apply lratCheckerSound f2118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2118
  · intro a ha; simp [p2118] at ha; subst a; trivial
  · exact checked2118
theorem derived2118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2118 := by
  apply localUnsat_implies_entails f2118 [c2103, c2110, c89, c376, c92, c103, c976, c2108, c2092, c369, c2111, c2115, c2117, c9, c57, c39, c176, c318, c333, c127, c191, c25, c192, c278, c2061, c44, c305] c2118 unsat2118 (by rfl) a
  have h0 : Entails.eval a c2103 := derived2103 a h
  have h1 : Entails.eval a c2110 := derived2110 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c976 := derived976 a h
  have h7 : Entails.eval a c2108 := derived2108 a h
  have h8 : Entails.eval a c2092 := derived2092 a h
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c2111 := derived2111 a h
  have h11 : Entails.eval a c2115 := derived2115 a h
  have h12 : Entails.eval a c2117 := derived2117 a h
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c318 := h 317 (by decide)
  have h18 : Entails.eval a c333 := h 332 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c191 := h 190 (by decide)
  have h21 : Entails.eval a c25 := h 24 (by decide)
  have h22 : Entails.eval a c192 := h 191 (by decide)
  have h23 : Entails.eval a c278 := h 277 (by decide)
  have h24 : Entails.eval a c2061 := derived2061 a h
  have h25 : Entails.eval a c44 := h 43 (by decide)
  have h26 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2119 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2103, some c2092, some c2110, some c89, some c376, some c92, some c103, some c2118, some c2068, some c76, some c365, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2119 : lratChecker f2119 p2119 = .success := by decide +kernel
theorem unsat2119 : Unsatisfiable (PosFin 57) f2119 := by
  apply lratCheckerSound f2119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2119
  · intro a ha; simp [p2119] at ha; subst a; trivial
  · exact checked2119
theorem derived2119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2119 := by
  apply localUnsat_implies_entails f2119 [c2103, c2092, c2110, c89, c376, c92, c103, c2118, c2068, c76, c365] c2119 unsat2119 (by rfl) a
  have h0 : Entails.eval a c2103 := derived2103 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c2110 := derived2110 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c2118 := derived2118 a h
  have h8 : Entails.eval a c2068 := derived2068 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2120 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2119, some c2108, some c2103, some c2092, some c841, some c359, some c372, some c976, some c368, some c363, some c103, some c66, some c2068, some c373, some c2042, some c2038, some c2037, some c315, some c334, some c57, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2120 : lratChecker f2120 p2120 = .success := by decide +kernel
theorem unsat2120 : Unsatisfiable (PosFin 57) f2120 := by
  apply lratCheckerSound f2120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2120
  · intro a ha; simp [p2120] at ha; subst a; trivial
  · exact checked2120
theorem derived2120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2120 := by
  apply localUnsat_implies_entails f2120 [c2119, c2108, c2103, c2092, c841, c359, c372, c976, c368, c363, c103, c66, c2068, c373, c2042, c2038, c2037, c315, c334, c57] c2120 unsat2120 (by rfl) a
  have h0 : Entails.eval a c2119 := derived2119 a h
  have h1 : Entails.eval a c2108 := derived2108 a h
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c976 := derived976 a h
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c2068 := derived2068 a h
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c2042 := derived2042 a h
  have h15 : Entails.eval a c2038 := derived2038 a h
  have h16 : Entails.eval a c2037 := derived2037 a h
  have h17 : Entails.eval a c315 := h 314 (by decide)
  have h18 : Entails.eval a c334 := h 333 (by decide)
  have h19 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2121 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2119, some c2108, some c369, some c368, some c358, some c359, some c1700, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2121 : lratChecker f2121 p2121 = .success := by decide +kernel
theorem unsat2121 : Unsatisfiable (PosFin 57) f2121 := by
  apply lratCheckerSound f2121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2121
  · intro a ha; simp [p2121] at ha; subst a; trivial
  · exact checked2121
theorem derived2121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2121 := by
  apply localUnsat_implies_entails f2121 [c2119, c2108, c369, c368, c358, c359, c1700] c2121 unsat2121 (by rfl) a
  have h0 : Entails.eval a c2119 := derived2119 a h
  have h1 : Entails.eval a c2108 := derived2108 a h
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c1700 := derived1700 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2122 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2103, some c2092, some c2120, some c89, some c2121, some c2068, some c365, some c76, some c103, some c2069, some c92, some c2042, some c315, some c334, some c57, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2122 : lratChecker f2122 p2122 = .success := by decide +kernel
theorem unsat2122 : Unsatisfiable (PosFin 57) f2122 := by
  apply lratCheckerSound f2122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2122
  · intro a ha; simp [p2122] at ha; subst a; trivial
  · exact checked2122
theorem derived2122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2122 := by
  apply localUnsat_implies_entails f2122 [c2103, c2092, c2120, c89, c2121, c2068, c365, c76, c103, c2069, c92, c2042, c315, c334, c57] c2122 unsat2122 (by rfl) a
  have h0 : Entails.eval a c2103 := derived2103 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c2120 := derived2120 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c2121 := derived2121 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c365 := h 364 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c2069 := derived2069 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c2042 := derived2042 a h
  have h12 : Entails.eval a c315 := h 314 (by decide)
  have h13 : Entails.eval a c334 := h 333 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2123 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c2122, some c2103, some c2092, some c367, some c2035, some c2068, some c2032, some c2052, some c2002, some c103, some c1085, some c320, some c333, some c968, some c2001, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2123 : lratChecker f2123 p2123 = .success := by decide +kernel
theorem unsat2123 : Unsatisfiable (PosFin 57) f2123 := by
  apply lratCheckerSound f2123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2123
  · intro a ha; simp [p2123] at ha; subst a; trivial
  · exact checked2123
theorem derived2123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2123 := by
  apply localUnsat_implies_entails f2123 [c380, c2122, c2103, c2092, c367, c2035, c2068, c2032, c2052, c2002, c103, c1085, c320, c333, c968, c2001] c2123 unsat2123 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c2122 := derived2122 a h
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2068 := derived2068 a h
  have h7 : Entails.eval a c2032 := derived2032 a h
  have h8 : Entails.eval a c2052 := derived2052 a h
  have h9 : Entails.eval a c2002 := derived2002 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c333 := h 332 (by decide)
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c2001 := derived2001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2124 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c2122, some c2103, some c2092, some c380, some c2123, some c361, some c363, some c968, some c365, some c103, some c2032, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2124 : lratChecker f2124 p2124 = .success := by decide +kernel
theorem unsat2124 : Unsatisfiable (PosFin 57) f2124 := by
  apply lratCheckerSound f2124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2124
  · intro a ha; simp [p2124] at ha; subst a; trivial
  · exact checked2124
theorem derived2124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2124 := by
  apply localUnsat_implies_entails f2124 [c841, c2122, c2103, c2092, c380, c2123, c361, c363, c968, c365, c103, c2032] c2124 unsat2124 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c2122 := derived2122 a h
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c2123 := derived2123 a h
  have h6 : Entails.eval a c361 := h 360 (by decide)
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c968 := derived968 a h
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c2032 := derived2032 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2125 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, false), (⟨44, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c2035, some c2068, some c2032, some c373, some c103, some c1085, some c69, some c372, some c151, some c956, some c9, some c152, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2125 : lratChecker f2125 p2125 = .success := by decide +kernel
theorem unsat2125 : Unsatisfiable (PosFin 57) f2125 := by
  apply lratCheckerSound f2125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2125
  · intro a ha; simp [p2125] at ha; subst a; trivial
  · exact checked2125
theorem derived2125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2125 := by
  apply localUnsat_implies_entails f2125 [c841, c2035, c2068, c2032, c373, c103, c1085, c69, c372, c151, c956, c9, c152] c2125 unsat2125 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c2035 := derived2035 a h
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c1085 := derived1085 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c956 := derived956 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2126 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c2092, some c2103, some c2122, some c2124, some c2125, some c367, some c365, some c363, some c373, some c2066, some c361, some c2070, some c1170, some c275, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2126 : lratChecker f2126 p2126 = .success := by decide +kernel
theorem unsat2126 : Unsatisfiable (PosFin 57) f2126 := by
  apply lratCheckerSound f2126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2126
  · intro a ha; simp [p2126] at ha; subst a; trivial
  · exact checked2126
theorem derived2126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2126 := by
  apply localUnsat_implies_entails f2126 [c841, c2092, c2103, c2122, c2124, c2125, c367, c365, c363, c373, c2066, c361, c2070, c1170, c275] c2126 unsat2126 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c2122 := derived2122 a h
  have h4 : Entails.eval a c2124 := derived2124 a h
  have h5 : Entails.eval a c2125 := derived2125 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c373 := h 372 (by decide)
  have h10 : Entails.eval a c2066 := derived2066 a h
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c2070 := derived2070 a h
  have h13 : Entails.eval a c1170 := derived1170 a h
  have h14 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2127 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c373, some c2066, some c342, some c323, some c56, some c191, some c334, some c25, some c192, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2127 : lratChecker f2127 p2127 = .success := by decide +kernel
theorem unsat2127 : Unsatisfiable (PosFin 57) f2127 := by
  apply lratCheckerSound f2127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2127
  · intro a ha; simp [p2127] at ha; subst a; trivial
  · exact checked2127
theorem derived2127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2127 := by
  apply localUnsat_implies_entails f2127 [c103, c373, c2066, c342, c323, c56, c191, c334, c25, c192] c2127 unsat2127 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c2066 := derived2066 a h
  have h3 : Entails.eval a c342 := h 341 (by decide)
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c334 := h 333 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2128 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c2092, some c2103, some c2122, some c2124, some c2125, some c367, some c365, some c363, some c373, some c2066, some c361, some c2126, some c103, some c597, some c294, some c359, some c277, some c2127, some c57, some c334, some c317, some c192, some c191, some c25, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2128 : lratChecker f2128 p2128 = .success := by decide +kernel
theorem unsat2128 : Unsatisfiable (PosFin 57) f2128 := by
  apply lratCheckerSound f2128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2128
  · intro a ha; simp [p2128] at ha; subst a; trivial
  · exact checked2128
theorem derived2128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2128 := by
  apply localUnsat_implies_entails f2128 [c841, c2092, c2103, c2122, c2124, c2125, c367, c365, c363, c373, c2066, c361, c2126, c103, c597, c294, c359, c277, c2127, c57, c334, c317, c192, c191, c25] c2128 unsat2128 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c2122 := derived2122 a h
  have h4 : Entails.eval a c2124 := derived2124 a h
  have h5 : Entails.eval a c2125 := derived2125 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c373 := h 372 (by decide)
  have h10 : Entails.eval a c2066 := derived2066 a h
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c2126 := derived2126 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c597 := derived597 a h
  have h15 : Entails.eval a c294 := h 293 (by decide)
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c2127 := derived2127 a h
  have h19 : Entails.eval a c57 := h 56 (by decide)
  have h20 : Entails.eval a c334 := h 333 (by decide)
  have h21 : Entails.eval a c317 := h 316 (by decide)
  have h22 : Entails.eval a c192 := h 191 (by decide)
  have h23 : Entails.eval a c191 := h 190 (by decide)
  have h24 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2129 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2122, some c2103, some c2092, some c841, some c2124, some c2125, some c367, some c365, some c363, some c373, some c2126, some c103, some c2128, some c598, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2129 : lratChecker f2129 p2129 = .success := by decide +kernel
theorem unsat2129 : Unsatisfiable (PosFin 57) f2129 := by
  apply lratCheckerSound f2129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2129
  · intro a ha; simp [p2129] at ha; subst a; trivial
  · exact checked2129
theorem derived2129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2129 := by
  apply localUnsat_implies_entails f2129 [c2122, c2103, c2092, c841, c2124, c2125, c367, c365, c363, c373, c2126, c103, c2128, c598] c2129 unsat2129 (by rfl) a
  have h0 : Entails.eval a c2122 := derived2122 a h
  have h1 : Entails.eval a c2103 := derived2103 a h
  have h2 : Entails.eval a c2092 := derived2092 a h
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c2124 := derived2124 a h
  have h5 : Entails.eval a c2125 := derived2125 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c373 := h 372 (by decide)
  have h10 : Entails.eval a c2126 := derived2126 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c2128 := derived2128 a h
  have h13 : Entails.eval a c598 := derived598 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2130 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨16, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2122, some c2129, some c2106, some c89, some c376, some c361, some c1700, some c96, some c1226, some c180, some c2103, some c2092, some c315, some c148, some c2025, some c2050, some c275, some c333, some c45, some c2001, some c296, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2130 : lratChecker f2130 p2130 = .success := by decide +kernel
theorem unsat2130 : Unsatisfiable (PosFin 57) f2130 := by
  apply lratCheckerSound f2130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2130
  · intro a ha; simp [p2130] at ha; subst a; trivial
  · exact checked2130
theorem derived2130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2130 := by
  apply localUnsat_implies_entails f2130 [c2122, c2129, c2106, c89, c376, c361, c1700, c96, c1226, c180, c2103, c2092, c315, c148, c2025, c2050, c275, c333, c45, c2001, c296] c2130 unsat2130 (by rfl) a
  have h0 : Entails.eval a c2122 := derived2122 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c2106 := derived2106 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c1700 := derived1700 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1226 := derived1226 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c2103 := derived2103 a h
  have h11 : Entails.eval a c2092 := derived2092 a h
  have h12 : Entails.eval a c315 := h 314 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c2025 := derived2025 a h
  have h15 : Entails.eval a c2050 := derived2050 a h
  have h16 : Entails.eval a c275 := h 274 (by decide)
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c45 := h 44 (by decide)
  have h19 : Entails.eval a c2001 := derived2001 a h
  have h20 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2131 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2122, some c2129, some c2106, some c89, some c376, some c361, some c1700, some c96, some c1226, some c180, some c2103, some c2130, some c57, some c39, some c333, some c336, some c132, some c2001, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2131 : lratChecker f2131 p2131 = .success := by decide +kernel
theorem unsat2131 : Unsatisfiable (PosFin 57) f2131 := by
  apply lratCheckerSound f2131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2131
  · intro a ha; simp [p2131] at ha; subst a; trivial
  · exact checked2131
theorem derived2131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2131 := by
  apply localUnsat_implies_entails f2131 [c2122, c2129, c2106, c89, c376, c361, c1700, c96, c1226, c180, c2103, c2130, c57, c39, c333, c336, c132, c2001] c2131 unsat2131 (by rfl) a
  have h0 : Entails.eval a c2122 := derived2122 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c2106 := derived2106 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c1700 := derived1700 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1226 := derived1226 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c2103 := derived2103 a h
  have h11 : Entails.eval a c2130 := derived2130 a h
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c333 := h 332 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c132 := h 131 (by decide)
  have h17 : Entails.eval a c2001 := derived2001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2132 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨13, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c365, some c69, some c323, some c315, some c146, some c2025, some c2050, some c37, some c274, some c319, some c298, some c266, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2132 : lratChecker f2132 p2132 = .success := by decide +kernel
theorem unsat2132 : Unsatisfiable (PosFin 57) f2132 := by
  apply lratCheckerSound f2132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2132
  · intro a ha; simp [p2132] at ha; subst a; trivial
  · exact checked2132
theorem derived2132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2132 := by
  apply localUnsat_implies_entails f2132 [c365, c69, c323, c315, c146, c2025, c2050, c37, c274, c319, c298, c266] c2132 unsat2132 (by rfl) a
  have h0 : Entails.eval a c365 := h 364 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c2025 := derived2025 a h
  have h6 : Entails.eval a c2050 := derived2050 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c298 := h 297 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2133 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2122, some c2129, some c2106, some c89, some c376, some c361, some c1700, some c96, some c1226, some c180, some c154, some c2103, some c92, some c103, some c152, some c9, some c2092, some c365, some c2131, some c163, some c167, some c2132, some c57, some c39, some c333, some c336, some c319, some c283, some c2001, some c266, some c2067, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked2133 : lratChecker f2133 p2133 = .success := by decide +kernel
theorem unsat2133 : Unsatisfiable (PosFin 57) f2133 := by
  apply lratCheckerSound f2133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2133
  · intro a ha; simp [p2133] at ha; subst a; trivial
  · exact checked2133
theorem derived2133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2133 := by
  apply localUnsat_implies_entails f2133 [c2122, c2129, c2106, c89, c376, c361, c1700, c96, c1226, c180, c154, c2103, c92, c103, c152, c9, c2092, c365, c2131, c163, c167, c2132, c57, c39, c333, c336, c319, c283, c2001, c266, c2067] c2133 unsat2133 (by rfl) a
  have h0 : Entails.eval a c2122 := derived2122 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c2106 := derived2106 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c1700 := derived1700 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1226 := derived1226 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c2103 := derived2103 a h
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c2092 := derived2092 a h
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c2131 := derived2131 a h
  have h19 : Entails.eval a c163 := h 162 (by decide)
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c2132 := derived2132 a h
  have h22 : Entails.eval a c57 := h 56 (by decide)
  have h23 : Entails.eval a c39 := h 38 (by decide)
  have h24 : Entails.eval a c333 := h 332 (by decide)
  have h25 : Entails.eval a c336 := h 335 (by decide)
  have h26 : Entails.eval a c319 := h 318 (by decide)
  have h27 : Entails.eval a c283 := h 282 (by decide)
  have h28 : Entails.eval a c2001 := derived2001 a h
  have h29 : Entails.eval a c266 := h 265 (by decide)
  have h30 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2134 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2035, some c103, some c2056, some c962, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2134 : lratChecker f2134 p2134 = .success := by decide +kernel
theorem unsat2134 : Unsatisfiable (PosFin 57) f2134 := by
  apply lratCheckerSound f2134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2134
  · intro a ha; simp [p2134] at ha; subst a; trivial
  · exact checked2134
theorem derived2134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2134 := by
  apply localUnsat_implies_entails f2134 [c2035, c103, c2056, c962] c2134 unsat2134 (by rfl) a
  have h0 : Entails.eval a c2035 := derived2035 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c2056 := derived2056 a h
  have h3 : Entails.eval a c962 := derived962 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2135 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2050, some c56, some c345, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2135 : lratChecker f2135 p2135 = .success := by decide +kernel
theorem unsat2135 : Unsatisfiable (PosFin 57) f2135 := by
  apply lratCheckerSound f2135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2135
  · intro a ha; simp [p2135] at ha; subst a; trivial
  · exact checked2135
theorem derived2135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2135 := by
  apply localUnsat_implies_entails f2135 [c2050, c56, c345] c2135 unsat2135 (by rfl) a
  have h0 : Entails.eval a c2050 := derived2050 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2136 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c292, some c296, some c2061, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2136 : lratChecker f2136 p2136 = .success := by decide +kernel
theorem unsat2136 : Unsatisfiable (PosFin 57) f2136 := by
  apply lratCheckerSound f2136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2136
  · intro a ha; simp [p2136] at ha; subst a; trivial
  · exact checked2136
theorem derived2136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2136 := by
  apply localUnsat_implies_entails f2136 [c292, c296, c2061] c2136 unsat2136 (by rfl) a
  have h0 : Entails.eval a c292 := h 291 (by decide)
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c2061 := derived2061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2137 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2129, some c89, some c2122, some c2106, some c376, some c361, some c2133, some c2035, some c2136, some c2103, some c92, some c2134, some c103, some c2092, some c323, some c2135, some c2001, some c336, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2137 : lratChecker f2137 p2137 = .success := by decide +kernel
theorem unsat2137 : Unsatisfiable (PosFin 57) f2137 := by
  apply lratCheckerSound f2137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2137
  · intro a ha; simp [p2137] at ha; subst a; trivial
  · exact checked2137
theorem derived2137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2137 := by
  apply localUnsat_implies_entails f2137 [c2129, c89, c2122, c2106, c376, c361, c2133, c2035, c2136, c2103, c92, c2134, c103, c2092, c323, c2135, c2001, c336] c2137 unsat2137 (by rfl) a
  have h0 : Entails.eval a c2129 := derived2129 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c2122 := derived2122 a h
  have h3 : Entails.eval a c2106 := derived2106 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c2133 := derived2133 a h
  have h7 : Entails.eval a c2035 := derived2035 a h
  have h8 : Entails.eval a c2136 := derived2136 a h
  have h9 : Entails.eval a c2103 := derived2103 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c2134 := derived2134 a h
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c2092 := derived2092 a h
  have h14 : Entails.eval a c323 := h 322 (by decide)
  have h15 : Entails.eval a c2135 := derived2135 a h
  have h16 : Entails.eval a c2001 := derived2001 a h
  have h17 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2138 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2122, some c2129, some c2106, some c89, some c376, some c361, some c2103, some c2133, some c2035, some c2136, some c2137, some c57, some c333, some c336, some c2001, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2138 : lratChecker f2138 p2138 = .success := by decide +kernel
theorem unsat2138 : Unsatisfiable (PosFin 57) f2138 := by
  apply lratCheckerSound f2138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2138
  · intro a ha; simp [p2138] at ha; subst a; trivial
  · exact checked2138
theorem derived2138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2138 := by
  apply localUnsat_implies_entails f2138 [c2122, c2129, c2106, c89, c376, c361, c2103, c2133, c2035, c2136, c2137, c57, c333, c336, c2001] c2138 unsat2138 (by rfl) a
  have h0 : Entails.eval a c2122 := derived2122 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c2106 := derived2106 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c2103 := derived2103 a h
  have h7 : Entails.eval a c2133 := derived2133 a h
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c2136 := derived2136 a h
  have h10 : Entails.eval a c2137 := derived2137 a h
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c2001 := derived2001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2139 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2129, some c89, some c2103, some c2092, some c376, some c92, some c103, some c2138, some c2068, some c76, some c365, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2139 : lratChecker f2139 p2139 = .success := by decide +kernel
theorem unsat2139 : Unsatisfiable (PosFin 57) f2139 := by
  apply lratCheckerSound f2139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2139
  · intro a ha; simp [p2139] at ha; subst a; trivial
  · exact checked2139
theorem derived2139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2139 := by
  apply localUnsat_implies_entails f2139 [c2129, c89, c2103, c2092, c376, c92, c103, c2138, c2068, c76, c365] c2139 unsat2139 (by rfl) a
  have h0 : Entails.eval a c2129 := derived2129 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c2103 := derived2103 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c2138 := derived2138 a h
  have h8 : Entails.eval a c2068 := derived2068 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2140 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2103, some c2129, some c92, some c103, some c2092, some c2139, some c2122, some c152, some c9, some c151, some c372, some c69, some c89, some c361, some c1240, some c1700, some c96, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2140 : lratChecker f2140 p2140 = .success := by decide +kernel
theorem unsat2140 : Unsatisfiable (PosFin 57) f2140 := by
  apply lratCheckerSound f2140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2140
  · intro a ha; simp [p2140] at ha; subst a; trivial
  · exact checked2140
theorem derived2140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2140 := by
  apply localUnsat_implies_entails f2140 [c2103, c2129, c92, c103, c2092, c2139, c2122, c152, c9, c151, c372, c69, c89, c361, c1240, c1700, c96] c2140 unsat2140 (by rfl) a
  have h0 : Entails.eval a c2103 := derived2103 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c2092 := derived2092 a h
  have h5 : Entails.eval a c2139 := derived2139 a h
  have h6 : Entails.eval a c2122 := derived2122 a h
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c361 := h 360 (by decide)
  have h14 : Entails.eval a c1240 := derived1240 a h
  have h15 : Entails.eval a c1700 := derived1700 a h
  have h16 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2141 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2103, some c2129, some c92, some c103, some c2092, some c2139, some c2122, some c152, some c9, some c151, some c372, some c76, some c283, some c277, some c45, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2141 : lratChecker f2141 p2141 = .success := by decide +kernel
theorem unsat2141 : Unsatisfiable (PosFin 57) f2141 := by
  apply lratCheckerSound f2141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2141
  · intro a ha; simp [p2141] at ha; subst a; trivial
  · exact checked2141
theorem derived2141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2141 := by
  apply localUnsat_implies_entails f2141 [c2103, c2129, c92, c103, c2092, c2139, c2122, c152, c9, c151, c372, c76, c283, c277, c45] c2141 unsat2141 (by rfl) a
  have h0 : Entails.eval a c2103 := derived2103 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c2092 := derived2092 a h
  have h5 : Entails.eval a c2139 := derived2139 a h
  have h6 : Entails.eval a c2122 := derived2122 a h
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c277 := h 276 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2142 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c323, some c267, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2142 : lratChecker f2142 p2142 = .success := by decide +kernel
theorem unsat2142 : Unsatisfiable (PosFin 57) f2142 := by
  apply lratCheckerSound f2142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2142
  · intro a ha; simp [p2142] at ha; subst a; trivial
  · exact checked2142
theorem derived2142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2142 := by
  apply localUnsat_implies_entails f2142 [c328, c323, c267] c2142 unsat2142 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2143 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2139, some c2129, some c2122, some c2103, some c2092, some c152, some c92, some c9, some c103, some c151, some c372, some c76, some c2140, some c2002, some c2141, some c2142, some c57, some c320, some c317, some c267, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2143 : lratChecker f2143 p2143 = .success := by decide +kernel
theorem unsat2143 : Unsatisfiable (PosFin 57) f2143 := by
  apply lratCheckerSound f2143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2143
  · intro a ha; simp [p2143] at ha; subst a; trivial
  · exact checked2143
theorem derived2143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2143 := by
  apply localUnsat_implies_entails f2143 [c2139, c2129, c2122, c2103, c2092, c152, c92, c9, c103, c151, c372, c76, c2140, c2002, c2141, c2142, c57, c320, c317, c267] c2143 unsat2143 (by rfl) a
  have h0 : Entails.eval a c2139 := derived2139 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c2122 := derived2122 a h
  have h3 : Entails.eval a c2103 := derived2103 a h
  have h4 : Entails.eval a c2092 := derived2092 a h
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c2140 := derived2140 a h
  have h13 : Entails.eval a c2002 := derived2002 a h
  have h14 : Entails.eval a c2141 := derived2141 a h
  have h15 : Entails.eval a c2142 := derived2142 a h
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c320 := h 319 (by decide)
  have h18 : Entails.eval a c317 := h 316 (by decide)
  have h19 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2144 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨5, by decide⟩, true), (⟨43, by decide⟩, false), (⟨32, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c2135, some c2142, some c334, some c413, some c269, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2144 : lratChecker f2144 p2144 = .success := by decide +kernel
theorem unsat2144 : Unsatisfiable (PosFin 57) f2144 := by
  apply lratCheckerSound f2144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2144
  · intro a ha; simp [p2144] at ha; subst a; trivial
  · exact checked2144
theorem derived2144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2144 := by
  apply localUnsat_implies_entails f2144 [c328, c2135, c2142, c334, c413, c269] c2144 unsat2144 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c2135 := derived2135 a h
  have h2 : Entails.eval a c2142 := derived2142 a h
  have h3 : Entails.eval a c334 := h 333 (by decide)
  have h4 : Entails.eval a c413 := derived413 a h
  have h5 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2145 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2129, some c89, some c2143, some c377, some c2139, some c2122, some c2103, some c2092, some c367, some c370, some c2002, some c2032, some c358, some c103, some c2144, some c57, some c39, some c320, some c317, some c283, some c267, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2145 : lratChecker f2145 p2145 = .success := by decide +kernel
theorem unsat2145 : Unsatisfiable (PosFin 57) f2145 := by
  apply lratCheckerSound f2145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2145
  · intro a ha; simp [p2145] at ha; subst a; trivial
  · exact checked2145
theorem derived2145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2145 := by
  apply localUnsat_implies_entails f2145 [c2129, c89, c2143, c377, c2139, c2122, c2103, c2092, c367, c370, c2002, c2032, c358, c103, c2144, c57, c39, c320, c317, c283, c267] c2145 unsat2145 (by rfl) a
  have h0 : Entails.eval a c2129 := derived2129 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c2143 := derived2143 a h
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c2139 := derived2139 a h
  have h5 : Entails.eval a c2122 := derived2122 a h
  have h6 : Entails.eval a c2103 := derived2103 a h
  have h7 : Entails.eval a c2092 := derived2092 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c2002 := derived2002 a h
  have h11 : Entails.eval a c2032 := derived2032 a h
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c2144 := derived2144 a h
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c320 := h 319 (by decide)
  have h18 : Entails.eval a c317 := h 316 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2146 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨4, by decide⟩, false), (⟨48, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2129, some c89, some c2143, some c2103, some c103, some c2135, some c334, some c377, some c96, some c2139, some c2122, some c2092, some c365, some c1414, some c315, some c69, some c2025, some c1240, some c275, some c9, some c45, some c165, some c294, some c15, some c192, some c180, some c248, some c29, some c188, some c114, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2146 : lratChecker f2146 p2146 = .success := by decide +kernel
theorem unsat2146 : Unsatisfiable (PosFin 57) f2146 := by
  apply lratCheckerSound f2146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2146
  · intro a ha; simp [p2146] at ha; subst a; trivial
  · exact checked2146
theorem derived2146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2146 := by
  apply localUnsat_implies_entails f2146 [c2129, c89, c2143, c2103, c103, c2135, c334, c377, c96, c2139, c2122, c2092, c365, c1414, c315, c69, c2025, c1240, c275, c9, c45, c165, c294, c15, c192, c180, c248, c29, c188, c114] c2146 unsat2146 (by rfl) a
  have h0 : Entails.eval a c2129 := derived2129 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c2143 := derived2143 a h
  have h3 : Entails.eval a c2103 := derived2103 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c2135 := derived2135 a h
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c2139 := derived2139 a h
  have h10 : Entails.eval a c2122 := derived2122 a h
  have h11 : Entails.eval a c2092 := derived2092 a h
  have h12 : Entails.eval a c365 := h 364 (by decide)
  have h13 : Entails.eval a c1414 := derived1414 a h
  have h14 : Entails.eval a c315 := h 314 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c2025 := derived2025 a h
  have h17 : Entails.eval a c1240 := derived1240 a h
  have h18 : Entails.eval a c275 := h 274 (by decide)
  have h19 : Entails.eval a c9 := h 8 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c294 := h 293 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c192 := h 191 (by decide)
  have h25 : Entails.eval a c180 := h 179 (by decide)
  have h26 : Entails.eval a c248 := h 247 (by decide)
  have h27 : Entails.eval a c29 := h 28 (by decide)
  have h28 : Entails.eval a c188 := h 187 (by decide)
  have h29 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2147 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨4, by decide⟩, false), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c2134, some c372, some c69, some c83, some c1240, some c9, some c159, some c165, some c183, some c15, some c180, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2147 : lratChecker f2147 p2147 = .success := by decide +kernel
theorem unsat2147 : Unsatisfiable (PosFin 57) f2147 := by
  apply lratCheckerSound f2147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2147
  · intro a ha; simp [p2147] at ha; subst a; trivial
  · exact checked2147
theorem derived2147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2147 := by
  apply localUnsat_implies_entails f2147 [c103, c2134, c372, c69, c83, c1240, c9, c159, c165, c183, c15, c180] c2147 unsat2147 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c2134 := derived2134 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c1240 := derived1240 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c159 := h 158 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2148 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2145, some c2129, some c89, some c2143, some c377, some c96, some c2139, some c2122, some c2103, some c2092, some c103, some c2147, some c365, some c1414, some c2146, some c69, some c57, some c39, some c1240, some c334, some c275, some c9, some c2061, some c165, some c294, some c15, some c192, some c180, some c248, some c29, some c188, some c114, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked2148 : lratChecker f2148 p2148 = .success := by decide +kernel
theorem unsat2148 : Unsatisfiable (PosFin 57) f2148 := by
  apply lratCheckerSound f2148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2148
  · intro a ha; simp [p2148] at ha; subst a; trivial
  · exact checked2148
theorem derived2148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2148 := by
  apply localUnsat_implies_entails f2148 [c2145, c2129, c89, c2143, c377, c96, c2139, c2122, c2103, c2092, c103, c2147, c365, c1414, c2146, c69, c57, c39, c1240, c334, c275, c9, c2061, c165, c294, c15, c192, c180, c248, c29, c188, c114] c2148 unsat2148 (by rfl) a
  have h0 : Entails.eval a c2145 := derived2145 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c2143 := derived2143 a h
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c2139 := derived2139 a h
  have h7 : Entails.eval a c2122 := derived2122 a h
  have h8 : Entails.eval a c2103 := derived2103 a h
  have h9 : Entails.eval a c2092 := derived2092 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c2147 := derived2147 a h
  have h12 : Entails.eval a c365 := h 364 (by decide)
  have h13 : Entails.eval a c1414 := derived1414 a h
  have h14 : Entails.eval a c2146 := derived2146 a h
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c39 := h 38 (by decide)
  have h18 : Entails.eval a c1240 := derived1240 a h
  have h19 : Entails.eval a c334 := h 333 (by decide)
  have h20 : Entails.eval a c275 := h 274 (by decide)
  have h21 : Entails.eval a c9 := h 8 (by decide)
  have h22 : Entails.eval a c2061 := derived2061 a h
  have h23 : Entails.eval a c165 := h 164 (by decide)
  have h24 : Entails.eval a c294 := h 293 (by decide)
  have h25 : Entails.eval a c15 := h 14 (by decide)
  have h26 : Entails.eval a c192 := h 191 (by decide)
  have h27 : Entails.eval a c180 := h 179 (by decide)
  have h28 : Entails.eval a c248 := h 247 (by decide)
  have h29 : Entails.eval a c29 := h 28 (by decide)
  have h30 : Entails.eval a c188 := h 187 (by decide)
  have h31 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2149 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2143, some c2129, some c89, some c2122, some c2092, some c2032, some c2070, some c1170, some c275, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2149 : lratChecker f2149 p2149 = .success := by decide +kernel
theorem unsat2149 : Unsatisfiable (PosFin 57) f2149 := by
  apply lratCheckerSound f2149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2149
  · intro a ha; simp [p2149] at ha; subst a; trivial
  · exact checked2149
theorem derived2149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2149 := by
  apply localUnsat_implies_entails f2149 [c2143, c2129, c89, c2122, c2092, c2032, c2070, c1170, c275] c2149 unsat2149 (by rfl) a
  have h0 : Entails.eval a c2143 := derived2143 a h
  have h1 : Entails.eval a c2129 := derived2129 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c2122 := derived2122 a h
  have h4 : Entails.eval a c2092 := derived2092 a h
  have h5 : Entails.eval a c2032 := derived2032 a h
  have h6 : Entails.eval a c2070 := derived2070 a h
  have h7 : Entails.eval a c1170 := derived1170 a h
  have h8 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2150 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2103, some c2149, some c103, some c2148, some c2068, some c76, some c365, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2150 : lratChecker f2150 p2150 = .success := by decide +kernel
theorem unsat2150 : Unsatisfiable (PosFin 57) f2150 := by
  apply lratCheckerSound f2150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2150
  · intro a ha; simp [p2150] at ha; subst a; trivial
  · exact checked2150
theorem derived2150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2150 := by
  apply localUnsat_implies_entails f2150 [c2092, c2103, c2149, c103, c2148, c2068, c76, c365] c2150 unsat2150 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2103 := derived2103 a h
  have h2 : Entails.eval a c2149 := derived2149 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c2148 := derived2148 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2151 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c368, some c78, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2151 : lratChecker f2151 p2151 = .success := by decide +kernel
theorem unsat2151 : Unsatisfiable (PosFin 57) f2151 := by
  apply lratCheckerSound f2151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2151
  · intro a ha; simp [p2151] at ha; subst a; trivial
  · exact checked2151
theorem derived2151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2151 := by
  apply localUnsat_implies_entails f2151 [c369, c368, c78] c2151 unsat2151 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2152 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨10, by decide⟩, true), (⟨44, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c367, some c365, some c2094, some c96, some c361, some c378, some c374, some c173, some c169, some c183, some c181, some c167, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2152 : lratChecker f2152 p2152 = .success := by decide +kernel
theorem unsat2152 : Unsatisfiable (PosFin 57) f2152 := by
  apply lratCheckerSound f2152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2152
  · intro a ha; simp [p2152] at ha; subst a; trivial
  · exact checked2152
theorem derived2152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2152 := by
  apply localUnsat_implies_entails f2152 [c2092, c367, c365, c2094, c96, c361, c378, c374, c173, c169, c183, c181, c167] c2152 unsat2152 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c173 := h 172 (by decide)
  have h9 : Entails.eval a c169 := h 168 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c181 := h 180 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2153 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2150, some c101, some c152, some c6, some c2152, some c2027, some c372, some c82, some c1517, some c12, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2153 : lratChecker f2153 p2153 = .success := by decide +kernel
theorem unsat2153 : Unsatisfiable (PosFin 57) f2153 := by
  apply lratCheckerSound f2153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2153
  · intro a ha; simp [p2153] at ha; subst a; trivial
  · exact checked2153
theorem derived2153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2153 := by
  apply localUnsat_implies_entails f2153 [c2092, c2150, c101, c152, c6, c2152, c2027, c372, c82, c1517, c12] c2153 unsat2153 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c2152 := derived2152 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c1517 := derived1517 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2154 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c2092, some c101, some c2151, some c152, some c6, some c2152, some c2035, some c2027, some c372, some c2153, some c370, some c361, some c2094, some c374, some c96, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2154 : lratChecker f2154 p2154 = .success := by decide +kernel
theorem unsat2154 : Unsatisfiable (PosFin 57) f2154 := by
  apply lratCheckerSound f2154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2154
  · intro a ha; simp [p2154] at ha; subst a; trivial
  · exact checked2154
theorem derived2154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2154 := by
  apply localUnsat_implies_entails f2154 [c2150, c2092, c101, c2151, c152, c6, c2152, c2035, c2027, c372, c2153, c370, c361, c2094, c374, c96] c2154 unsat2154 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2151 := derived2151 a h
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c2152 := derived2152 a h
  have h7 : Entails.eval a c2035 := derived2035 a h
  have h8 : Entails.eval a c2027 := derived2027 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c2153 := derived2153 a h
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c361 := h 360 (by decide)
  have h13 : Entails.eval a c2094 := derived2094 a h
  have h14 : Entails.eval a c374 := h 373 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2155 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c2154, some c68, some c1251, some c2151, some c102, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2155 : lratChecker f2155 p2155 = .success := by decide +kernel
theorem unsat2155 : Unsatisfiable (PosFin 57) f2155 := by
  apply lratCheckerSound f2155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2155
  · intro a ha; simp [p2155] at ha; subst a; trivial
  · exact checked2155
theorem derived2155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2155 := by
  apply localUnsat_implies_entails f2155 [c2150, c2154, c68, c1251, c2151, c102] c2155 unsat2155 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c2154 := derived2154 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c1251 := derived1251 a h
  have h4 : Entails.eval a c2151 := derived2151 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2156 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c367, some c2035, some c2027, some c1125, some c1509, some c1654, some c70, some c290, some c330, some c2025, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2156 : lratChecker f2156 p2156 = .success := by decide +kernel
theorem unsat2156 : Unsatisfiable (PosFin 57) f2156 := by
  apply lratCheckerSound f2156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2156
  · intro a ha; simp [p2156] at ha; subst a; trivial
  · exact checked2156
theorem derived2156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2156 := by
  apply localUnsat_implies_entails f2156 [c2092, c367, c2035, c2027, c1125, c1509, c1654, c70, c290, c330, c2025] c2156 unsat2156 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c2027 := derived2027 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1509 := derived1509 a h
  have h6 : Entails.eval a c1654 := derived1654 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c2025 := derived2025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2157 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨4, by decide⟩, false), (⟨42, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1601, some c1594, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2157 : lratChecker f2157 p2157 = .success := by decide +kernel
theorem unsat2157 : Unsatisfiable (PosFin 57) f2157 := by
  apply lratCheckerSound f2157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2157
  · intro a ha; simp [p2157] at ha; subst a; trivial
  · exact checked2157
theorem derived2157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2157 := by
  apply localUnsat_implies_entails f2157 [c1601, c1594] c2157 unsat2157 (by rfl) a
  have h0 : Entails.eval a c1601 := derived1601 a h
  have h1 : Entails.eval a c1594 := derived1594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2158 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨48, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c72, some c79, some c1126, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2158 : lratChecker f2158 p2158 = .success := by decide +kernel
theorem unsat2158 : Unsatisfiable (PosFin 57) f2158 := by
  apply lratCheckerSound f2158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2158
  · intro a ha; simp [p2158] at ha; subst a; trivial
  · exact checked2158
theorem derived2158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2158 := by
  apply localUnsat_implies_entails f2158 [c2092, c72, c79, c1126] c2158 unsat2158 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1126 := derived1126 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2159 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c176, some c183, some c171, some c1068, some c2045, some c2048, some c237, some c338, some c298, some c193, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p2159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2159 : lratChecker f2159 p2159 = .success := by decide +kernel
theorem unsat2159 : Unsatisfiable (PosFin 57) f2159 := by
  apply lratCheckerSound f2159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2159
  · intro a ha; simp [p2159] at ha; subst a; trivial
  · exact checked2159
theorem derived2159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2159 := by
  apply localUnsat_implies_entails f2159 [c176, c183, c171, c1068, c2045, c2048, c237, c338, c298, c193] c2159 unsat2159 (by rfl) a
  have h0 : Entails.eval a c176 := h 175 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c1068 := derived1068 a h
  have h4 : Entails.eval a c2045 := derived2045 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2160 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨16, by decide⟩, false), (⟨55, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c365, some c2155, some c160, some c1480, some c2150, some c101, some c96, some c2159, some c12, some c1524, some c1543, some c1663, some c2062, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2160 : lratChecker f2160 p2160 = .success := by decide +kernel
theorem unsat2160 : Unsatisfiable (PosFin 57) f2160 := by
  apply lratCheckerSound f2160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2160
  · intro a ha; simp [p2160] at ha; subst a; trivial
  · exact checked2160
theorem derived2160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2160 := by
  apply localUnsat_implies_entails f2160 [c2092, c365, c2155, c160, c1480, c2150, c101, c96, c2159, c12, c1524, c1543, c1663, c2062] c2160 unsat2160 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c2155 := derived2155 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c1480 := derived1480 a h
  have h5 : Entails.eval a c2150 := derived2150 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c2159 := derived2159 a h
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c1524 := derived1524 a h
  have h11 : Entails.eval a c1543 := derived1543 a h
  have h12 : Entails.eval a c1663 := derived1663 a h
  have h13 : Entails.eval a c2062 := derived2062 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2161 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨48, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c101, some c2155, some c2092, some c365, some c2094, some c96, some c2158, some c1601, some c2157, some c156, some c363, some c8, some c160, some c1480, some c2160, some c359, some c1209, some c2036, some c1509, some c1599, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2161 : lratChecker f2161 p2161 = .success := by decide +kernel
theorem unsat2161 : Unsatisfiable (PosFin 57) f2161 := by
  apply lratCheckerSound f2161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2161
  · intro a ha; simp [p2161] at ha; subst a; trivial
  · exact checked2161
theorem derived2161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2161 := by
  apply localUnsat_implies_entails f2161 [c2150, c101, c2155, c2092, c365, c2094, c96, c2158, c1601, c2157, c156, c363, c8, c160, c1480, c2160, c359, c1209, c2036, c1509, c1599] c2161 unsat2161 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2155 := derived2155 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c2094 := derived2094 a h
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c2158 := derived2158 a h
  have h8 : Entails.eval a c1601 := derived1601 a h
  have h9 : Entails.eval a c2157 := derived2157 a h
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c1480 := derived1480 a h
  have h15 : Entails.eval a c2160 := derived2160 a h
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c1209 := derived1209 a h
  have h18 : Entails.eval a c2036 := derived2036 a h
  have h19 : Entails.eval a c1509 := derived1509 a h
  have h20 : Entails.eval a c1599 := derived1599 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2162 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c101, some c2155, some c2092, some c2161, some c2035, some c2027, some c372, some c1125, some c1509, some c2094, some c96, some c1593, some c2158, some c1599, some c1594, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2162 : lratChecker f2162 p2162 = .success := by decide +kernel
theorem unsat2162 : Unsatisfiable (PosFin 57) f2162 := by
  apply lratCheckerSound f2162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2162
  · intro a ha; simp [p2162] at ha; subst a; trivial
  · exact checked2162
theorem derived2162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2162 := by
  apply localUnsat_implies_entails f2162 [c2150, c101, c2155, c2092, c2161, c2035, c2027, c372, c1125, c1509, c2094, c96, c1593, c2158, c1599, c1594] c2162 unsat2162 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2155 := derived2155 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c2161 := derived2161 a h
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c1125 := derived1125 a h
  have h9 : Entails.eval a c1509 := derived1509 a h
  have h10 : Entails.eval a c2094 := derived2094 a h
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c1593 := derived1593 a h
  have h13 : Entails.eval a c2158 := derived2158 a h
  have h14 : Entails.eval a c1599 := derived1599 a h
  have h15 : Entails.eval a c1594 := derived1594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2163 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2155, some c2150, some c2092, some c101, some c2162, some c367, some c2156, some c2027, some c152, some c2153, some c372, some c1125, some c1509, some c6, some c327, some c1619, some c287, some c157, some c160, some c196, some c181, some c24, some c236, some c109, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2163 : lratChecker f2163 p2163 = .success := by decide +kernel
theorem unsat2163 : Unsatisfiable (PosFin 57) f2163 := by
  apply lratCheckerSound f2163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2163
  · intro a ha; simp [p2163] at ha; subst a; trivial
  · exact checked2163
theorem derived2163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2163 := by
  apply localUnsat_implies_entails f2163 [c2155, c2150, c2092, c101, c2162, c367, c2156, c2027, c152, c2153, c372, c1125, c1509, c6, c327, c1619, c287, c157, c160, c196, c181, c24, c236, c109] c2163 unsat2163 (by rfl) a
  have h0 : Entails.eval a c2155 := derived2155 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c2092 := derived2092 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c2162 := derived2162 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c2156 := derived2156 a h
  have h7 : Entails.eval a c2027 := derived2027 a h
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c2153 := derived2153 a h
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c1125 := derived1125 a h
  have h12 : Entails.eval a c1509 := derived1509 a h
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c1619 := derived1619 a h
  have h16 : Entails.eval a c287 := h 286 (by decide)
  have h17 : Entails.eval a c157 := h 156 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c196 := h 195 (by decide)
  have h20 : Entails.eval a c181 := h 180 (by decide)
  have h21 : Entails.eval a c24 := h 23 (by decide)
  have h22 : Entails.eval a c236 := h 235 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2164 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2163, some c92, some c68, some c1586, some c2027, some c367, some c365, some c2094, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2164 : lratChecker f2164 p2164 = .success := by decide +kernel
theorem unsat2164 : Unsatisfiable (PosFin 57) f2164 := by
  apply lratCheckerSound f2164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2164
  · intro a ha; simp [p2164] at ha; subst a; trivial
  · exact checked2164
theorem derived2164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2164 := by
  apply localUnsat_implies_entails f2164 [c2092, c2163, c92, c68, c1586, c2027, c367, c365, c2094] c2164 unsat2164 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2163 := derived2163 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c1586 := derived1586 a h
  have h5 : Entails.eval a c2027 := derived2027 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c2094 := derived2094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2165 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1715, some c2025, some c291, some c290, some c52, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2165 : lratChecker f2165 p2165 = .success := by decide +kernel
theorem unsat2165 : Unsatisfiable (PosFin 57) f2165 := by
  apply lratCheckerSound f2165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2165
  · intro a ha; simp [p2165] at ha; subst a; trivial
  · exact checked2165
theorem derived2165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2165 := by
  apply localUnsat_implies_entails f2165 [c1715, c2025, c291, c290, c52] c2165 unsat2165 (by rfl) a
  have h0 : Entails.eval a c1715 := derived1715 a h
  have h1 : Entails.eval a c2025 := derived2025 a h
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2166 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c2164, some c100, some c92, some c68, some c1251, some c2037, some c102, some c2165, some c70, some c1461, some c2087, some c60, some c64, some c325, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2166 : lratChecker f2166 p2166 = .success := by decide +kernel
theorem unsat2166 : Unsatisfiable (PosFin 57) f2166 := by
  apply lratCheckerSound f2166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2166
  · intro a ha; simp [p2166] at ha; subst a; trivial
  · exact checked2166
theorem derived2166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2166 := by
  apply localUnsat_implies_entails f2166 [c2150, c2164, c100, c92, c68, c1251, c2037, c102, c2165, c70, c1461, c2087, c60, c64, c325] c2166 unsat2166 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c2164 := derived2164 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c1251 := derived1251 a h
  have h6 : Entails.eval a c2037 := derived2037 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c2165 := derived2165 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c1461 := derived1461 a h
  have h11 : Entails.eval a c2087 := derived2087 a h
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2167 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c365, some c2027, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p2167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2167 : lratChecker f2167 p2167 = .success := by decide +kernel
theorem unsat2167 : Unsatisfiable (PosFin 57) f2167 := by
  apply lratCheckerSound f2167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2167
  · intro a ha; simp [p2167] at ha; subst a; trivial
  · exact checked2167
theorem derived2167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2167 := by
  apply localUnsat_implies_entails f2167 [c372, c365, c2027] c2167 unsat2167 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c2027 := derived2027 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2168 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2150, some c100, some c2167, some c101, some c2166, some c2151, some c2156, some c2094, some c96, some c377, some c2158, some c356, some c1578, some c379, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2168 : lratChecker f2168 p2168 = .success := by decide +kernel
theorem unsat2168 : Unsatisfiable (PosFin 57) f2168 := by
  apply lratCheckerSound f2168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2168
  · intro a ha; simp [p2168] at ha; subst a; trivial
  · exact checked2168
theorem derived2168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2168 := by
  apply localUnsat_implies_entails f2168 [c2092, c2150, c100, c2167, c101, c2166, c2151, c2156, c2094, c96, c377, c2158, c356, c1578, c379] c2168 unsat2168 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c2167 := derived2167 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c2166 := derived2166 a h
  have h6 : Entails.eval a c2151 := derived2151 a h
  have h7 : Entails.eval a c2156 := derived2156 a h
  have h8 : Entails.eval a c2094 := derived2094 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c2158 := derived2158 a h
  have h12 : Entails.eval a c356 := h 355 (by decide)
  have h13 : Entails.eval a c1578 := derived1578 a h
  have h14 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2169 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c367, some c2035, some c2150, some c100, some c2167, some c101, some c2166, some c373, some c2165, some c987, some c70, some c376, some c370, some c356, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2169 : lratChecker f2169 p2169 = .success := by decide +kernel
theorem unsat2169 : Unsatisfiable (PosFin 57) f2169 := by
  apply lratCheckerSound f2169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2169
  · intro a ha; simp [p2169] at ha; subst a; trivial
  · exact checked2169
theorem derived2169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2169 := by
  apply localUnsat_implies_entails f2169 [c2092, c367, c2035, c2150, c100, c2167, c101, c2166, c373, c2165, c987, c70, c376, c370, c356] c2169 unsat2169 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c2150 := derived2150 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2167 := derived2167 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c2166 := derived2166 a h
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c2165 := derived2165 a h
  have h10 : Entails.eval a c987 := derived987 a h
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2170 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c100, some c101, some c2092, some c367, some c2035, some c2027, some c1125, some c1509, some c2169, some c96, some c290, some c330, some c2025, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2170 : lratChecker f2170 p2170 = .success := by decide +kernel
theorem unsat2170 : Unsatisfiable (PosFin 57) f2170 := by
  apply lratCheckerSound f2170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2170
  · intro a ha; simp [p2170] at ha; subst a; trivial
  · exact checked2170
theorem derived2170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2170 := by
  apply localUnsat_implies_entails f2170 [c2150, c100, c101, c2092, c367, c2035, c2027, c1125, c1509, c2169, c96, c290, c330, c2025] c2170 unsat2170 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c1125 := derived1125 a h
  have h8 : Entails.eval a c1509 := derived1509 a h
  have h9 : Entails.eval a c2169 := derived2169 a h
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c2025 := derived2025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2171 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨45, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c2094, some c363, some c69, some c153, some c374, some c12, some c165, some c8, some c173, some c169, some c183, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2171 : lratChecker f2171 p2171 = .success := by decide +kernel
theorem unsat2171 : Unsatisfiable (PosFin 57) f2171 := by
  apply lratCheckerSound f2171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2171
  · intro a ha; simp [p2171] at ha; subst a; trivial
  · exact checked2171
theorem derived2171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2171 := by
  apply localUnsat_implies_entails f2171 [c100, c2094, c363, c69, c153, c374, c12, c165, c8, c173, c169, c183] c2171 unsat2171 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2172 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2166, some c2150, some c2092, some c101, some c100, some c2167, some c2168, some c2170, some c2094, some c96, some c377, some c2158, some c2171, some c379, some c67, some c2036, some c1125, some c1509, some c290, some c330, some c2025, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2172 : lratChecker f2172 p2172 = .success := by decide +kernel
theorem unsat2172 : Unsatisfiable (PosFin 57) f2172 := by
  apply lratCheckerSound f2172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2172
  · intro a ha; simp [p2172] at ha; subst a; trivial
  · exact checked2172
theorem derived2172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2172 := by
  apply localUnsat_implies_entails f2172 [c2166, c2150, c2092, c101, c100, c2167, c2168, c2170, c2094, c96, c377, c2158, c2171, c379, c67, c2036, c1125, c1509, c290, c330, c2025] c2172 unsat2172 (by rfl) a
  have h0 : Entails.eval a c2166 := derived2166 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c2092 := derived2092 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c2167 := derived2167 a h
  have h6 : Entails.eval a c2168 := derived2168 a h
  have h7 : Entails.eval a c2170 := derived2170 a h
  have h8 : Entails.eval a c2094 := derived2094 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c2158 := derived2158 a h
  have h12 : Entails.eval a c2171 := derived2171 a h
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c2036 := derived2036 a h
  have h16 : Entails.eval a c1125 := derived1125 a h
  have h17 : Entails.eval a c1509 := derived1509 a h
  have h18 : Entails.eval a c290 := h 289 (by decide)
  have h19 : Entails.eval a c330 := h 329 (by decide)
  have h20 : Entails.eval a c2025 := derived2025 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2173 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2092, some c2027, some c2032, some c1586, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2173 : lratChecker f2173 p2173 = .success := by decide +kernel
theorem unsat2173 : Unsatisfiable (PosFin 57) f2173 := by
  apply lratCheckerSound f2173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2173
  · intro a ha; simp [p2173] at ha; subst a; trivial
  · exact checked2173
theorem derived2173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2173 := by
  apply localUnsat_implies_entails f2173 [c2172, c2092, c2027, c2032, c1586] c2173 unsat2173 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c2027 := derived2027 a h
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c1586 := derived1586 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2174 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2167, some c2173, some c367, some c2094, some c2172, some c2166, some c1548, some c96, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2174 : lratChecker f2174 p2174 = .success := by decide +kernel
theorem unsat2174 : Unsatisfiable (PosFin 57) f2174 := by
  apply lratCheckerSound f2174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2174
  · intro a ha; simp [p2174] at ha; subst a; trivial
  · exact checked2174
theorem derived2174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2174 := by
  apply localUnsat_implies_entails f2174 [c2092, c2167, c2173, c367, c2094, c2172, c2166, c1548, c96] c2174 unsat2174 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2167 := derived2167 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c2172 := derived2172 a h
  have h6 : Entails.eval a c2166 := derived2166 a h
  have h7 : Entails.eval a c1548 := derived1548 a h
  have h8 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2175 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2166, some c2150, some c2092, some c2173, some c367, some c2174, some c102, some c1590, some c81, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2175 : lratChecker f2175 p2175 = .success := by decide +kernel
theorem unsat2175 : Unsatisfiable (PosFin 57) f2175 := by
  apply lratCheckerSound f2175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2175
  · intro a ha; simp [p2175] at ha; subst a; trivial
  · exact checked2175
theorem derived2175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2175 := by
  apply localUnsat_implies_entails f2175 [c2172, c2166, c2150, c2092, c2173, c367, c2174, c102, c1590, c81] c2175 unsat2175 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c2150 := derived2150 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c2173 := derived2173 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c2174 := derived2174 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c1590 := derived1590 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2176 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2175, some c2166, some c2150, some c377, some c341, some c301, some c1287, some c1951, some c151, some c337, some c297, some c266, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2176 : lratChecker f2176 p2176 = .success := by decide +kernel
theorem unsat2176 : Unsatisfiable (PosFin 57) f2176 := by
  apply lratCheckerSound f2176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2176
  · intro a ha; simp [p2176] at ha; subst a; trivial
  · exact checked2176
theorem derived2176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2176 := by
  apply localUnsat_implies_entails f2176 [c2175, c2166, c2150, c377, c341, c301, c1287, c1951, c151, c337, c297, c266] c2176 unsat2176 (by rfl) a
  have h0 : Entails.eval a c2175 := derived2175 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c2150 := derived2150 a h
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c1951 := derived1951 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c337 := h 336 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2177 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2175, some c2166, some c153, some c362, some c10, some c369, some c151, some c356, some c376, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2177 : lratChecker f2177 p2177 = .success := by decide +kernel
theorem unsat2177 : Unsatisfiable (PosFin 57) f2177 := by
  apply lratCheckerSound f2177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2177
  · intro a ha; simp [p2177] at ha; subst a; trivial
  · exact checked2177
theorem derived2177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2177 := by
  apply localUnsat_implies_entails f2177 [c2175, c2166, c153, c362, c10, c369, c151, c356, c376] c2177 unsat2177 (by rfl) a
  have h0 : Entails.eval a c2175 := derived2175 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2178 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨19, by decide⟩, true), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c337, some c297, some c191, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2178 : lratChecker f2178 p2178 = .success := by decide +kernel
theorem unsat2178 : Unsatisfiable (PosFin 57) f2178 := by
  apply lratCheckerSound f2178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2178
  · intro a ha; simp [p2178] at ha; subst a; trivial
  · exact checked2178
theorem derived2178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2178 := by
  apply localUnsat_implies_entails f2178 [c337, c297, c191] c2178 unsat2178 (by rfl) a
  have h0 : Entails.eval a c337 := h 336 (by decide)
  have h1 : Entails.eval a c297 := h 296 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2179 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c2175, some c2166, some c2150, some c5, some c10, some c1282, some c1345, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2179 : lratChecker f2179 p2179 = .success := by decide +kernel
theorem unsat2179 : Unsatisfiable (PosFin 57) f2179 := by
  apply lratCheckerSound f2179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2179
  · intro a ha; simp [p2179] at ha; subst a; trivial
  · exact checked2179
theorem derived2179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2179 := by
  apply localUnsat_implies_entails f2179 [c95, c2175, c2166, c2150, c5, c10, c1282, c1345] c2179 unsat2179 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c2175 := derived2175 a h
  have h2 : Entails.eval a c2166 := derived2166 a h
  have h3 : Entails.eval a c2150 := derived2150 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1345 := derived1345 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2180 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2176, some c2175, some c2166, some c2177, some c151, some c284, some c324, some c2178, some c193, some c26, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2180 : lratChecker f2180 p2180 = .success := by decide +kernel
theorem unsat2180 : Unsatisfiable (PosFin 57) f2180 := by
  apply lratCheckerSound f2180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2180
  · intro a ha; simp [p2180] at ha; subst a; trivial
  · exact checked2180
theorem derived2180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2180 := by
  apply localUnsat_implies_entails f2180 [c2176, c2175, c2166, c2177, c151, c284, c324, c2178, c193, c26] c2180 unsat2180 (by rfl) a
  have h0 : Entails.eval a c2176 := derived2176 a h
  have h1 : Entails.eval a c2175 := derived2175 a h
  have h2 : Entails.eval a c2166 := derived2166 a h
  have h3 : Entails.eval a c2177 := derived2177 a h
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c2178 := derived2178 a h
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2180

end CochromaticTwenty.Certificates.B16_8_2
