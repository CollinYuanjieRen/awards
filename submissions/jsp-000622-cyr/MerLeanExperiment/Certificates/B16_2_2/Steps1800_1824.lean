import MerLeanExperiment.Certificates.B16_2_2.Steps1700_1799

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2184 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2175, some c2056, some c2174, some c2048, some c2182, some c2181, some c184, some c195, some c5, some c18, some c173, some c363, some c2183, some c25, some c241, some c2177, some c2070, some c98, some c369, some c377, some c364, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2184 : lratChecker f2184 p2184 = .success := by decide +kernel
theorem unsat2184 : Unsatisfiable (PosFin 57) f2184 := by
  apply lratCheckerSound f2184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2184
  · intro a ha; simp [p2184] at ha; subst a; trivial
  · exact checked2184
theorem derived2184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2184 := by
  apply localUnsat_implies_entails f2184 [c2131, c2165, c2175, c2056, c2174, c2048, c2182, c2181, c184, c195, c5, c18, c173, c363, c2183, c25, c241, c2177, c2070, c98, c369, c377, c364] c2184 unsat2184 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2175 := derived2175 a h
  have h3 : Entails.eval a c2056 := derived2056 a h
  have h4 : Entails.eval a c2174 := derived2174 a h
  have h5 : Entails.eval a c2048 := derived2048 a h
  have h6 : Entails.eval a c2182 := derived2182 a h
  have h7 : Entails.eval a c2181 := derived2181 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c363 := h 362 (by decide)
  have h14 : Entails.eval a c2183 := derived2183 a h
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c241 := h 240 (by decide)
  have h17 : Entails.eval a c2177 := derived2177 a h
  have h18 : Entails.eval a c2070 := derived2070 a h
  have h19 : Entails.eval a c98 := h 97 (by decide)
  have h20 : Entails.eval a c369 := h 368 (by decide)
  have h21 : Entails.eval a c377 := h 376 (by decide)
  have h22 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2185 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2174, some c2175, some c2056, some c2184, some c4, some c76, some c195, some c18, some c173, some c78, some c26, some c242, some c125, some c2067, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2185 : lratChecker f2185 p2185 = .success := by decide +kernel
theorem unsat2185 : Unsatisfiable (PosFin 57) f2185 := by
  apply lratCheckerSound f2185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2185
  · intro a ha; simp [p2185] at ha; subst a; trivial
  · exact checked2185
theorem derived2185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2185 := by
  apply localUnsat_implies_entails f2185 [c2131, c2165, c2174, c2175, c2056, c2184, c4, c76, c195, c18, c173, c78, c26, c242, c125, c2067] c2185 unsat2185 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2174 := derived2174 a h
  have h3 : Entails.eval a c2175 := derived2175 a h
  have h4 : Entails.eval a c2056 := derived2056 a h
  have h5 : Entails.eval a c2184 := derived2184 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c242 := h 241 (by decide)
  have h14 : Entails.eval a c125 := h 124 (by decide)
  have h15 : Entails.eval a c2067 := derived2067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2186 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2185, some c2174, some c1008, some c181, some c196, some c2116, some c2140, some c2056, some c98, some c75, some c1014, some c2073, some c360, some c123, some c371, some c236, some c2052, some c263, some c38, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2186 : lratChecker f2186 p2186 = .success := by decide +kernel
theorem unsat2186 : Unsatisfiable (PosFin 57) f2186 := by
  apply lratCheckerSound f2186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2186
  · intro a ha; simp [p2186] at ha; subst a; trivial
  · exact checked2186
theorem derived2186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2186 := by
  apply localUnsat_implies_entails f2186 [c2131, c2165, c2185, c2174, c1008, c181, c196, c2116, c2140, c2056, c98, c75, c1014, c2073, c360, c123, c371, c236, c2052, c263, c38] c2186 unsat2186 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2185 := derived2185 a h
  have h3 : Entails.eval a c2174 := derived2174 a h
  have h4 : Entails.eval a c1008 := derived1008 a h
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c2116 := derived2116 a h
  have h8 : Entails.eval a c2140 := derived2140 a h
  have h9 : Entails.eval a c2056 := derived2056 a h
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c1014 := derived1014 a h
  have h13 : Entails.eval a c2073 := derived2073 a h
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c371 := h 370 (by decide)
  have h17 : Entails.eval a c236 := h 235 (by decide)
  have h18 : Entails.eval a c2052 := derived2052 a h
  have h19 : Entails.eval a c263 := h 262 (by decide)
  have h20 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2187 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c196, some c2116, some c5, some c18, some c2053, some c1790, some c38, some c125, some c2067, some c24, some c242, some c173, some c78, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2187 : lratChecker f2187 p2187 = .success := by decide +kernel
theorem unsat2187 : Unsatisfiable (PosFin 57) f2187 := by
  apply lratCheckerSound f2187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2187
  · intro a ha; simp [p2187] at ha; subst a; trivial
  · exact checked2187
theorem derived2187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2187 := by
  apply localUnsat_implies_entails f2187 [c2131, c2165, c196, c2116, c5, c18, c2053, c1790, c38, c125, c2067, c24, c242, c173, c78] c2187 unsat2187 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c2116 := derived2116 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c1790 := derived1790 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c2067 := derived2067 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c242 := h 241 (by decide)
  have h13 : Entails.eval a c173 := h 172 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2188 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c114, some c2070, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p2188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2188 : lratChecker f2188 p2188 = .success := by decide +kernel
theorem unsat2188 : Unsatisfiable (PosFin 57) f2188 := by
  apply lratCheckerSound f2188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2188
  · intro a ha; simp [p2188] at ha; subst a; trivial
  · exact checked2188
theorem derived2188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2188 := by
  apply localUnsat_implies_entails f2188 [c162, c114, c2070] c2188 unsat2188 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c2070 := derived2070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2189 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2131, some c2186, some c2048, some c2185, some c2174, some c2187, some c181, some c2084, some c2087, some c380, some c199, some c78, some c6, some c102, some c1790, some c38, some c2188, some c2053, some c121, some c173, some c24, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2189 : lratChecker f2189 p2189 = .success := by decide +kernel
theorem unsat2189 : Unsatisfiable (PosFin 57) f2189 := by
  apply lratCheckerSound f2189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2189
  · intro a ha; simp [p2189] at ha; subst a; trivial
  · exact checked2189
theorem derived2189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2189 := by
  apply localUnsat_implies_entails f2189 [c2165, c2131, c2186, c2048, c2185, c2174, c2187, c181, c2084, c2087, c380, c199, c78, c6, c102, c1790, c38, c2188, c2053, c121, c173, c24] c2189 unsat2189 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c2186 := derived2186 a h
  have h3 : Entails.eval a c2048 := derived2048 a h
  have h4 : Entails.eval a c2185 := derived2185 a h
  have h5 : Entails.eval a c2174 := derived2174 a h
  have h6 : Entails.eval a c2187 := derived2187 a h
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c2084 := derived2084 a h
  have h9 : Entails.eval a c2087 := derived2087 a h
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c1790 := derived1790 a h
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c2188 := derived2188 a h
  have h18 : Entails.eval a c2053 := derived2053 a h
  have h19 : Entails.eval a c121 := h 120 (by decide)
  have h20 : Entails.eval a c173 := h 172 (by decide)
  have h21 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2190 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2174, some c2185, some c2189, some c2056, some c2116, some c181, some c380, some c78, some c6, some c2055, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2190 : lratChecker f2190 p2190 = .success := by decide +kernel
theorem unsat2190 : Unsatisfiable (PosFin 57) f2190 := by
  apply lratCheckerSound f2190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2190
  · intro a ha; simp [p2190] at ha; subst a; trivial
  · exact checked2190
theorem derived2190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2190 := by
  apply localUnsat_implies_entails f2190 [c2165, c2174, c2185, c2189, c2056, c2116, c181, c380, c78, c6, c2055] c2190 unsat2190 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2174 := derived2174 a h
  have h2 : Entails.eval a c2185 := derived2185 a h
  have h3 : Entails.eval a c2189 := derived2189 a h
  have h4 : Entails.eval a c2056 := derived2056 a h
  have h5 : Entails.eval a c2116 := derived2116 a h
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c2055 := derived2055 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2191 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c192, some c1254, some c2039, some c4, some c2053, some c2046, some c17, some c103, some c80, some c2085, some c164, some c116, some c2070, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2191 : lratChecker f2191 p2191 = .success := by decide +kernel
theorem unsat2191 : Unsatisfiable (PosFin 57) f2191 := by
  apply lratCheckerSound f2191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2191
  · intro a ha; simp [p2191] at ha; subst a; trivial
  · exact checked2191
theorem derived2191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2191 := by
  apply localUnsat_implies_entails f2191 [c2131, c2165, c192, c1254, c2039, c4, c2053, c2046, c17, c103, c80, c2085, c164, c116, c2070] c2191 unsat2191 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c2039 := derived2039 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c2053 := derived2053 a h
  have h7 : Entails.eval a c2046 := derived2046 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c2085 := derived2085 a h
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c2070 := derived2070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2192 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2165, some c2190, some c1254, some c192, some c2046, some c2039, some c17, some c2053, some c1278, some c4, some c2166, some c2191, some c377, some c2058, some c164, some c91, some c89, some c161, some c1064, some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p2192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2192 : lratChecker f2192 p2192 = .success := by decide +kernel
theorem unsat2192 : Unsatisfiable (PosFin 57) f2192 := by
  apply lratCheckerSound f2192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2192
  · intro a ha; simp [p2192] at ha; subst a; trivial
  · exact checked2192
theorem derived2192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2192 := by
  apply localUnsat_implies_entails f2192 [c2131, c2165, c2190, c1254, c192, c2046, c2039, c17, c2053, c1278, c4, c2166, c2191, c377, c2058, c164, c91, c89, c161, c1064] c2192 unsat2192 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c2190 := derived2190 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c2046 := derived2046 a h
  have h6 : Entails.eval a c2039 := derived2039 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c2053 := derived2053 a h
  have h9 : Entails.eval a c1278 := derived1278 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c2166 := derived2166 a h
  have h12 : Entails.eval a c2191 := derived2191 a h
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c2058 := derived2058 a h
  have h15 : Entails.eval a c164 := h 163 (by decide)
  have h16 : Entails.eval a c91 := h 90 (by decide)
  have h17 : Entails.eval a c89 := h 88 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  have h19 : Entails.eval a c1064 := derived1064 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2193 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2192, some c1003, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p2193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2193 : lratChecker f2193 p2193 = .success := by decide +kernel
theorem unsat2193 : Unsatisfiable (PosFin 57) f2193 := by
  apply lratCheckerSound f2193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2193
  · intro a ha; simp [p2193] at ha; subst a; trivial
  · exact checked2193
theorem derived2193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2193 := by
  apply localUnsat_implies_entails f2193 [c2192, c1003] c2193 unsat2193 (by rfl) a
  have h0 : Entails.eval a c2192 := derived2192 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2194 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2193, some c2131, some c196, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p2194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2194 : lratChecker f2194 p2194 = .success := by decide +kernel
theorem unsat2194 : Unsatisfiable (PosFin 57) f2194 := by
  apply lratCheckerSound f2194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2194
  · intro a ha; simp [p2194] at ha; subst a; trivial
  · exact checked2194
theorem derived2194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2194 := by
  apply localUnsat_implies_entails f2194 [c2193, c2131, c196] c2194 unsat2194 (by rfl) a
  have h0 : Entails.eval a c2193 := derived2193 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2195 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2193, some c2131, some c195, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p2195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2195 : lratChecker f2195 p2195 = .success := by decide +kernel
theorem unsat2195 : Unsatisfiable (PosFin 57) f2195 := by
  apply lratCheckerSound f2195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2195
  · intro a ha; simp [p2195] at ha; subst a; trivial
  · exact checked2195
theorem derived2195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2195 := by
  apply localUnsat_implies_entails f2195 [c2193, c2131, c195] c2195 unsat2195 (by rfl) a
  have h0 : Entails.eval a c2193 := derived2193 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2196 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2195, some c2165, some c2193, some c2039, some c2053, some c2046, some c1318, some c25, some c39, some c161, some c116, some c2070, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2196 : lratChecker f2196 p2196 = .success := by decide +kernel
theorem unsat2196 : Unsatisfiable (PosFin 57) f2196 := by
  apply lratCheckerSound f2196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2196
  · intro a ha; simp [p2196] at ha; subst a; trivial
  · exact checked2196
theorem derived2196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2196 := by
  apply localUnsat_implies_entails f2196 [c2131, c2195, c2165, c2193, c2039, c2053, c2046, c1318, c25, c39, c161, c116, c2070] c2196 unsat2196 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2195 := derived2195 a h
  have h2 : Entails.eval a c2165 := derived2165 a h
  have h3 : Entails.eval a c2193 := derived2193 a h
  have h4 : Entails.eval a c2039 := derived2039 a h
  have h5 : Entails.eval a c2053 := derived2053 a h
  have h6 : Entails.eval a c2046 := derived2046 a h
  have h7 : Entails.eval a c1318 := derived1318 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c2070 := derived2070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2197 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2165, some c2193, some c2062, some c113, some c512, some c2070, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2197 : lratChecker f2197 p2197 = .success := by decide +kernel
theorem unsat2197 : Unsatisfiable (PosFin 57) f2197 := by
  apply lratCheckerSound f2197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2197
  · intro a ha; simp [p2197] at ha; subst a; trivial
  · exact checked2197
theorem derived2197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2197 := by
  apply localUnsat_implies_entails f2197 [c2165, c2193, c2062, c113, c512, c2070] c2197 unsat2197 (by rfl) a
  have h0 : Entails.eval a c2165 := derived2165 a h
  have h1 : Entails.eval a c2193 := derived2193 a h
  have h2 : Entails.eval a c2062 := derived2062 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c512 := derived512 a h
  have h5 : Entails.eval a c2070 := derived2070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2198 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2195, some c2039, some c2053, some c2196, some c2197, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2198 : lratChecker f2198 p2198 = .success := by decide +kernel
theorem unsat2198 : Unsatisfiable (PosFin 57) f2198 := by
  apply lratCheckerSound f2198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2198
  · intro a ha; simp [p2198] at ha; subst a; trivial
  · exact checked2198
theorem derived2198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2198 := by
  apply localUnsat_implies_entails f2198 [c2195, c2039, c2053, c2196, c2197] c2198 unsat2198 (by rfl) a
  have h0 : Entails.eval a c2195 := derived2195 a h
  have h1 : Entails.eval a c2039 := derived2039 a h
  have h2 : Entails.eval a c2053 := derived2053 a h
  have h3 : Entails.eval a c2196 := derived2196 a h
  have h4 : Entails.eval a c2197 := derived2197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2199 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2198, some c1254, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2199 : lratChecker f2199 p2199 = .success := by decide +kernel
theorem unsat2199 : Unsatisfiable (PosFin 57) f2199 := by
  apply lratCheckerSound f2199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2199
  · intro a ha; simp [p2199] at ha; subst a; trivial
  · exact checked2199
theorem derived2199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2199 := by
  apply localUnsat_implies_entails f2199 [c2198, c1254] c2199 unsat2199 (by rfl) a
  have h0 : Entails.eval a c2198 := derived2198 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2200 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2195, some c2131, some c2193, some c2165, some c2048, some c1992, some c1920, some c122, some c25, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2200 : lratChecker f2200 p2200 = .success := by decide +kernel
theorem unsat2200 : Unsatisfiable (PosFin 57) f2200 := by
  apply lratCheckerSound f2200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2200
  · intro a ha; simp [p2200] at ha; subst a; trivial
  · exact checked2200
theorem derived2200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2200 := by
  apply localUnsat_implies_entails f2200 [c2195, c2131, c2193, c2165, c2048, c1992, c1920, c122, c25] c2200 unsat2200 (by rfl) a
  have h0 : Entails.eval a c2195 := derived2195 a h
  have h1 : Entails.eval a c2131 := derived2131 a h
  have h2 : Entails.eval a c2193 := derived2193 a h
  have h3 : Entails.eval a c2165 := derived2165 a h
  have h4 : Entails.eval a c2048 := derived2048 a h
  have h5 : Entails.eval a c1992 := derived1992 a h
  have h6 : Entails.eval a c1920 := derived1920 a h
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2201 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2199, some c2192, some c2195, some c2194, some c2200, some c2056, some c802, some c2180, some c2072, some c334, some c156, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2201 : lratChecker f2201 p2201 = .success := by decide +kernel
theorem unsat2201 : Unsatisfiable (PosFin 57) f2201 := by
  apply lratCheckerSound f2201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2201
  · intro a ha; simp [p2201] at ha; subst a; trivial
  · exact checked2201
theorem derived2201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2201 := by
  apply localUnsat_implies_entails f2201 [c2199, c2192, c2195, c2194, c2200, c2056, c802, c2180, c2072, c334, c156] c2201 unsat2201 (by rfl) a
  have h0 : Entails.eval a c2199 := derived2199 a h
  have h1 : Entails.eval a c2192 := derived2192 a h
  have h2 : Entails.eval a c2195 := derived2195 a h
  have h3 : Entails.eval a c2194 := derived2194 a h
  have h4 : Entails.eval a c2200 := derived2200 a h
  have h5 : Entails.eval a c2056 := derived2056 a h
  have h6 : Entails.eval a c802 := derived802 a h
  have h7 : Entails.eval a c2180 := derived2180 a h
  have h8 : Entails.eval a c2072 := derived2072 a h
  have h9 : Entails.eval a c334 := h 333 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2202 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2195, some c2053, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p2202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2202 : lratChecker f2202 p2202 = .success := by decide +kernel
theorem unsat2202 : Unsatisfiable (PosFin 57) f2202 := by
  apply lratCheckerSound f2202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2202
  · intro a ha; simp [p2202] at ha; subst a; trivial
  · exact checked2202
theorem derived2202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2202 := by
  apply localUnsat_implies_entails f2202 [c2201, c2195, c2053] c2202 unsat2202 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2195 := derived2195 a h
  have h2 : Entails.eval a c2053 := derived2053 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2203 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2202, some c2201, some c2197, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p2203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2203 : lratChecker f2203 p2203 = .success := by decide +kernel
theorem unsat2203 : Unsatisfiable (PosFin 57) f2203 := by
  apply lratCheckerSound f2203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2203
  · intro a ha; simp [p2203] at ha; subst a; trivial
  · exact checked2203
theorem derived2203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2203 := by
  apply localUnsat_implies_entails f2203 [c2202, c2201, c2197] c2203 unsat2203 (by rfl) a
  have h0 : Entails.eval a c2202 := derived2202 a h
  have h1 : Entails.eval a c2201 := derived2201 a h
  have h2 : Entails.eval a c2197 := derived2197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2204 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2202, some c2198, some c2165, some c2193, some c1806, some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2204 : lratChecker f2204 p2204 = .success := by decide +kernel
theorem unsat2204 : Unsatisfiable (PosFin 57) f2204 := by
  apply lratCheckerSound f2204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2204
  · intro a ha; simp [p2204] at ha; subst a; trivial
  · exact checked2204
theorem derived2204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2204 := by
  apply localUnsat_implies_entails f2204 [c2202, c2198, c2165, c2193, c1806] c2204 unsat2204 (by rfl) a
  have h0 : Entails.eval a c2202 := derived2202 a h
  have h1 : Entails.eval a c2198 := derived2198 a h
  have h2 : Entails.eval a c2165 := derived2165 a h
  have h3 : Entails.eval a c2193 := derived2193 a h
  have h4 : Entails.eval a c1806 := derived1806 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2205 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2203, some c2165, some c25, some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p2205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2205 : lratChecker f2205 p2205 = .success := by decide +kernel
theorem unsat2205 : Unsatisfiable (PosFin 57) f2205 := by
  apply lratCheckerSound f2205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2205
  · intro a ha; simp [p2205] at ha; subst a; trivial
  · exact checked2205
theorem derived2205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2205 := by
  apply localUnsat_implies_entails f2205 [c2203, c2165, c25] c2205 unsat2205 (by rfl) a
  have h0 : Entails.eval a c2203 := derived2203 a h
  have h1 : Entails.eval a c2165 := derived2165 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2206 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2204, some c2192, some c376, some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p2206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2206 : lratChecker f2206 p2206 = .success := by decide +kernel
theorem unsat2206 : Unsatisfiable (PosFin 57) f2206 := by
  apply lratCheckerSound f2206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2206
  · intro a ha; simp [p2206] at ha; subst a; trivial
  · exact checked2206
theorem derived2206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2206 := by
  apply localUnsat_implies_entails f2206 [c2204, c2192, c376] c2206 unsat2206 (by rfl) a
  have h0 : Entails.eval a c2204 := derived2204 a h
  have h1 : Entails.eval a c2192 := derived2192 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2207 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2205, some c2202, some c2193, some c161, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2207 : lratChecker f2207 p2207 = .success := by decide +kernel
theorem unsat2207 : Unsatisfiable (PosFin 57) f2207 := by
  apply lratCheckerSound f2207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2207
  · intro a ha; simp [p2207] at ha; subst a; trivial
  · exact checked2207
theorem derived2207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2207 := by
  apply localUnsat_implies_entails f2207 [c2205, c2202, c2193, c161] c2207 unsat2207 (by rfl) a
  have h0 : Entails.eval a c2205 := derived2205 a h
  have h1 : Entails.eval a c2202 := derived2202 a h
  have h2 : Entails.eval a c2193 := derived2193 a h
  have h3 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2208 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f2208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2207, some c2206, some c2058]
def p2208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2208 : lratChecker f2208 p2208 = .success := by decide +kernel
theorem unsat2208 : Unsatisfiable (PosFin 57) f2208 := by
  apply lratCheckerSound f2208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2208
  · intro a ha; simp [p2208] at ha; subst a; trivial
  · exact checked2208
theorem derived2208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2208 := by
  apply localUnsat_implies_entails f2208 [c2207, c2206, c2058] c2208 unsat2208 (by rfl) a
  have h0 : Entails.eval a c2207 := derived2207 a h
  have h1 : Entails.eval a c2206 := derived2206 a h
  have h2 : Entails.eval a c2058 := derived2058 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived2208

end CochromaticTwenty.Certificates.B16_2_2
