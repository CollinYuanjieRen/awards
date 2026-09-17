import MerLeanExperiment.Certificates.B16_8_2.Steps1700_1799

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2181 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c367, some c2035, some c373, some c841, some c2172, some c2032, some c2175, some c2166, some c2150, some c1956, some c1280, some c95, some c2179, some c2180, some c1129, some c1287, some c334, some c1218, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2181 : lratChecker f2181 p2181 = .success := by decide +kernel
theorem unsat2181 : Unsatisfiable (PosFin 57) f2181 := by
  apply lratCheckerSound f2181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2181
  · intro a ha; simp [p2181] at ha; subst a; trivial
  · exact checked2181
theorem derived2181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2181 := by
  apply localUnsat_implies_entails f2181 [c2092, c367, c2035, c373, c841, c2172, c2032, c2175, c2166, c2150, c1956, c1280, c95, c2179, c2180, c1129, c1287, c334, c1218] c2181 unsat2181 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c2035 := derived2035 a h
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c2172 := derived2172 a h
  have h6 : Entails.eval a c2032 := derived2032 a h
  have h7 : Entails.eval a c2175 := derived2175 a h
  have h8 : Entails.eval a c2166 := derived2166 a h
  have h9 : Entails.eval a c2150 := derived2150 a h
  have h10 : Entails.eval a c1956 := derived1956 a h
  have h11 : Entails.eval a c1280 := derived1280 a h
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c2179 := derived2179 a h
  have h14 : Entails.eval a c2180 := derived2180 a h
  have h15 : Entails.eval a c1129 := derived1129 a h
  have h16 : Entails.eval a c1287 := derived1287 a h
  have h17 : Entails.eval a c334 := h 333 (by decide)
  have h18 : Entails.eval a c1218 := derived1218 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2182 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2092, some c367, some c2032, some c2035, some c2150, some c2181, some c102, some c2165, some c70, some c1461, some c2087, some c60, some c64, some c325, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2182 : lratChecker f2182 p2182 = .success := by decide +kernel
theorem unsat2182 : Unsatisfiable (PosFin 57) f2182 := by
  apply lratCheckerSound f2182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2182
  · intro a ha; simp [p2182] at ha; subst a; trivial
  · exact checked2182
theorem derived2182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2182 := by
  apply localUnsat_implies_entails f2182 [c2172, c2092, c367, c2032, c2035, c2150, c2181, c102, c2165, c70, c1461, c2087, c60, c64, c325] c2182 unsat2182 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2150 := derived2150 a h
  have h6 : Entails.eval a c2181 := derived2181 a h
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
def c2183 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2172, some c1280, some c1956, some c367, some c2032, some c2035, some c1300, some c374, some c2176, some c95, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2183 : lratChecker f2183 p2183 = .success := by decide +kernel
theorem unsat2183 : Unsatisfiable (PosFin 57) f2183 := by
  apply lratCheckerSound f2183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2183
  · intro a ha; simp [p2183] at ha; subst a; trivial
  · exact checked2183
theorem derived2183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2183 := by
  apply localUnsat_implies_entails f2183 [c2092, c2172, c1280, c1956, c367, c2032, c2035, c1300, c374, c2176, c95] c2183 unsat2183 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2172 := derived2172 a h
  have h2 : Entails.eval a c1280 := derived1280 a h
  have h3 : Entails.eval a c1956 := derived1956 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2032 := derived2032 a h
  have h6 : Entails.eval a c2035 := derived2035 a h
  have h7 : Entails.eval a c1300 := derived1300 a h
  have h8 : Entails.eval a c374 := h 373 (by decide)
  have h9 : Entails.eval a c2176 := derived2176 a h
  have h10 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2184 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2175, some c2166, some c2150, some c2180, some c2177, some c1951, some c284, some c324, some c334, some c294, some c264, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2184 : lratChecker f2184 p2184 = .success := by decide +kernel
theorem unsat2184 : Unsatisfiable (PosFin 57) f2184 := by
  apply lratCheckerSound f2184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2184
  · intro a ha; simp [p2184] at ha; subst a; trivial
  · exact checked2184
theorem derived2184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2184 := by
  apply localUnsat_implies_entails f2184 [c2175, c2166, c2150, c2180, c2177, c1951, c284, c324, c334, c294, c264] c2184 unsat2184 (by rfl) a
  have h0 : Entails.eval a c2175 := derived2175 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c2150 := derived2150 a h
  have h3 : Entails.eval a c2180 := derived2180 a h
  have h4 : Entails.eval a c2177 := derived2177 a h
  have h5 : Entails.eval a c1951 := derived1951 a h
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c334 := h 333 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2185 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2184, some c69, some c284, some c324, some c37, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2185 : lratChecker f2185 p2185 = .success := by decide +kernel
theorem unsat2185 : Unsatisfiable (PosFin 57) f2185 := by
  apply lratCheckerSound f2185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2185
  · intro a ha; simp [p2185] at ha; subst a; trivial
  · exact checked2185
theorem derived2185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2185 := by
  apply localUnsat_implies_entails f2185 [c2184, c69, c284, c324, c37] c2185 unsat2185 (by rfl) a
  have h0 : Entails.eval a c2184 := derived2184 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2186 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨8, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2183, some c2092, some c2172, some c1280, some c1956, some c367, some c2032, some c2035, some c2166, some c2185, some c2030, some c1325, some c300, some c358, some c1247, some c325, some c270, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2186 : lratChecker f2186 p2186 = .success := by decide +kernel
theorem unsat2186 : Unsatisfiable (PosFin 57) f2186 := by
  apply lratCheckerSound f2186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2186
  · intro a ha; simp [p2186] at ha; subst a; trivial
  · exact checked2186
theorem derived2186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2186 := by
  apply localUnsat_implies_entails f2186 [c2183, c2092, c2172, c1280, c1956, c367, c2032, c2035, c2166, c2185, c2030, c1325, c300, c358, c1247, c325, c270] c2186 unsat2186 (by rfl) a
  have h0 : Entails.eval a c2183 := derived2183 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c2172 := derived2172 a h
  have h3 : Entails.eval a c1280 := derived1280 a h
  have h4 : Entails.eval a c1956 := derived1956 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c2032 := derived2032 a h
  have h7 : Entails.eval a c2035 := derived2035 a h
  have h8 : Entails.eval a c2166 := derived2166 a h
  have h9 : Entails.eval a c2185 := derived2185 a h
  have h10 : Entails.eval a c2030 := derived2030 a h
  have h11 : Entails.eval a c1325 := derived1325 a h
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c1247 := derived1247 a h
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2187 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2172, some c1129, some c2175, some c2166, some c2150, some c334, some c1218, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2187 : lratChecker f2187 p2187 = .success := by decide +kernel
theorem unsat2187 : Unsatisfiable (PosFin 57) f2187 := by
  apply lratCheckerSound f2187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2187
  · intro a ha; simp [p2187] at ha; subst a; trivial
  · exact checked2187
theorem derived2187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2187 := by
  apply localUnsat_implies_entails f2187 [c2092, c2172, c1129, c2175, c2166, c2150, c334, c1218] c2187 unsat2187 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2172 := derived2172 a h
  have h2 : Entails.eval a c1129 := derived1129 a h
  have h3 : Entails.eval a c2175 := derived2175 a h
  have h4 : Entails.eval a c2166 := derived2166 a h
  have h5 : Entails.eval a c2150 := derived2150 a h
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c1218 := derived1218 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2188 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2092, some c367, some c2032, some c2175, some c2150, some c102, some c1956, some c1280, some c2183, some c2186, some c368, some c2187, some c1287, some c150, some c1325, some c5, some c7, some c174, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2188 : lratChecker f2188 p2188 = .success := by decide +kernel
theorem unsat2188 : Unsatisfiable (PosFin 57) f2188 := by
  apply lratCheckerSound f2188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2188
  · intro a ha; simp [p2188] at ha; subst a; trivial
  · exact checked2188
theorem derived2188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2188 := by
  apply localUnsat_implies_entails f2188 [c2172, c2092, c367, c2032, c2175, c2150, c102, c1956, c1280, c2183, c2186, c368, c2187, c1287, c150, c1325, c5, c7, c174] c2188 unsat2188 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2092 := derived2092 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c2032 := derived2032 a h
  have h4 : Entails.eval a c2175 := derived2175 a h
  have h5 : Entails.eval a c2150 := derived2150 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c1956 := derived1956 a h
  have h8 : Entails.eval a c1280 := derived1280 a h
  have h9 : Entails.eval a c2183 := derived2183 a h
  have h10 : Entails.eval a c2186 := derived2186 a h
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c2187 := derived2187 a h
  have h13 : Entails.eval a c1287 := derived1287 a h
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c1325 := derived1325 a h
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c7 := h 6 (by decide)
  have h18 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2189 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2182, some c2188, some c96, some c2092, some c367, some c2035, some c2172, some c2166, some c290, some c301, some c2059, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2189 : lratChecker f2189 p2189 = .success := by decide +kernel
theorem unsat2189 : Unsatisfiable (PosFin 57) f2189 := by
  apply lratCheckerSound f2189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2189
  · intro a ha; simp [p2189] at ha; subst a; trivial
  · exact checked2189
theorem derived2189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2189 := by
  apply localUnsat_implies_entails f2189 [c2182, c2188, c96, c2092, c367, c2035, c2172, c2166, c290, c301, c2059] c2189 unsat2189 (by rfl) a
  have h0 : Entails.eval a c2182 := derived2182 a h
  have h1 : Entails.eval a c2188 := derived2188 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c2035 := derived2035 a h
  have h6 : Entails.eval a c2172 := derived2172 a h
  have h7 : Entails.eval a c2166 := derived2166 a h
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c2059 := derived2059 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2190 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2166, some c2092, some c367, some c2035, some c2182, some c2188, some c96, some c2189, some c38, some c341, some c330, some c2033, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2190 : lratChecker f2190 p2190 = .success := by decide +kernel
theorem unsat2190 : Unsatisfiable (PosFin 57) f2190 := by
  apply lratCheckerSound f2190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2190
  · intro a ha; simp [p2190] at ha; subst a; trivial
  · exact checked2190
theorem derived2190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2190 := by
  apply localUnsat_implies_entails f2190 [c2172, c2166, c2092, c367, c2035, c2182, c2188, c96, c2189, c38, c341, c330, c2033] c2190 unsat2190 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c2092 := derived2092 a h
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2182 := derived2182 a h
  have h6 : Entails.eval a c2188 := derived2188 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c2189 := derived2189 a h
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c341 := h 340 (by decide)
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c2033 := derived2033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2191 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2190, some c81, some c1956, some c72, some c2166, some c2092, some c374, some c2035, some c2042, some c1414, some c1277, some c2176, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2191 : lratChecker f2191 p2191 = .success := by decide +kernel
theorem unsat2191 : Unsatisfiable (PosFin 57) f2191 := by
  apply lratCheckerSound f2191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2191
  · intro a ha; simp [p2191] at ha; subst a; trivial
  · exact checked2191
theorem derived2191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2191 := by
  apply localUnsat_implies_entails f2191 [c2172, c2190, c81, c1956, c72, c2166, c2092, c374, c2035, c2042, c1414, c1277, c2176] c2191 unsat2191 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2190 := derived2190 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c1956 := derived1956 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c2166 := derived2166 a h
  have h6 : Entails.eval a c2092 := derived2092 a h
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c2035 := derived2035 a h
  have h9 : Entails.eval a c2042 := derived2042 a h
  have h10 : Entails.eval a c1414 := derived1414 a h
  have h11 : Entails.eval a c1277 := derived1277 a h
  have h12 : Entails.eval a c2176 := derived2176 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2192 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨36, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2191, some c2172, some c2190, some c81, some c1956, some c2166, some c2185, some c1325, some c340, some c300, some c358, some c285, some c325, some c270, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2192 : lratChecker f2192 p2192 = .success := by decide +kernel
theorem unsat2192 : Unsatisfiable (PosFin 57) f2192 := by
  apply lratCheckerSound f2192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2192
  · intro a ha; simp [p2192] at ha; subst a; trivial
  · exact checked2192
theorem derived2192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2192 := by
  apply localUnsat_implies_entails f2192 [c2191, c2172, c2190, c81, c1956, c2166, c2185, c1325, c340, c300, c358, c285, c325, c270] c2192 unsat2192 (by rfl) a
  have h0 : Entails.eval a c2191 := derived2191 a h
  have h1 : Entails.eval a c2172 := derived2172 a h
  have h2 : Entails.eval a c2190 := derived2190 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c1956 := derived1956 a h
  have h5 : Entails.eval a c2166 := derived2166 a h
  have h6 : Entails.eval a c2185 := derived2185 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c340 := h 339 (by decide)
  have h9 : Entails.eval a c300 := h 299 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2193 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2150, some c102, some c2191, some c2172, some c2190, some c81, some c1956, some c2175, some c2092, some c2192, some c372, some c368, some c1129, some c281, some c2187, some c1287, some c83, some c191, some c150, some c1325, some c1318, some c7, some c174, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2193 : lratChecker f2193 p2193 = .success := by decide +kernel
theorem unsat2193 : Unsatisfiable (PosFin 57) f2193 := by
  apply lratCheckerSound f2193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2193
  · intro a ha; simp [p2193] at ha; subst a; trivial
  · exact checked2193
theorem derived2193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2193 := by
  apply localUnsat_implies_entails f2193 [c2150, c102, c2191, c2172, c2190, c81, c1956, c2175, c2092, c2192, c372, c368, c1129, c281, c2187, c1287, c83, c191, c150, c1325, c1318, c7, c174] c2193 unsat2193 (by rfl) a
  have h0 : Entails.eval a c2150 := derived2150 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c2191 := derived2191 a h
  have h3 : Entails.eval a c2172 := derived2172 a h
  have h4 : Entails.eval a c2190 := derived2190 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c1956 := derived1956 a h
  have h7 : Entails.eval a c2175 := derived2175 a h
  have h8 : Entails.eval a c2092 := derived2092 a h
  have h9 : Entails.eval a c2192 := derived2192 a h
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c1129 := derived1129 a h
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c2187 := derived2187 a h
  have h15 : Entails.eval a c1287 := derived1287 a h
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c191 := h 190 (by decide)
  have h18 : Entails.eval a c150 := h 149 (by decide)
  have h19 : Entails.eval a c1325 := derived1325 a h
  have h20 : Entails.eval a c1318 := derived1318 a h
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2194 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2150, some c102, some c2193, some c61, some c60, some c2033, some c347, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2194 : lratChecker f2194 p2194 = .success := by decide +kernel
theorem unsat2194 : Unsatisfiable (PosFin 57) f2194 := by
  apply lratCheckerSound f2194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2194
  · intro a ha; simp [p2194] at ha; subst a; trivial
  · exact checked2194
theorem derived2194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2194 := by
  apply localUnsat_implies_entails f2194 [c2172, c2150, c102, c2193, c61, c60, c2033, c347] c2194 unsat2194 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2150 := derived2150 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c2193 := derived2193 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c2033 := derived2033 a h
  have h7 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2195 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1623, some c2191, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2195 : lratChecker f2195 p2195 = .success := by decide +kernel
theorem unsat2195 : Unsatisfiable (PosFin 57) f2195 := by
  apply lratCheckerSound f2195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2195
  · intro a ha; simp [p2195] at ha; subst a; trivial
  · exact checked2195
theorem derived2195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2195 := by
  apply localUnsat_implies_entails f2195 [c1623, c2191] c2195 unsat2195 (by rfl) a
  have h0 : Entails.eval a c1623 := derived1623 a h
  have h1 : Entails.eval a c2191 := derived2191 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2196 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2166, some c2092, some c301, some c2059, some c48, some c290, some c275, some c2035, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2196 : lratChecker f2196 p2196 = .success := by decide +kernel
theorem unsat2196 : Unsatisfiable (PosFin 57) f2196 := by
  apply lratCheckerSound f2196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2196
  · intro a ha; simp [p2196] at ha; subst a; trivial
  · exact checked2196
theorem derived2196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2196 := by
  apply localUnsat_implies_entails f2196 [c2172, c2166, c2092, c301, c2059, c48, c290, c275, c2035] c2196 unsat2196 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c2092 := derived2092 a h
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c2059 := derived2059 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c2035 := derived2035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2197 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2194, some c2172, some c2166, some c2092, some c2196, some c38, some c341, some c2042, some c2033, some c2035, some c330, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2197 : lratChecker f2197 p2197 = .success := by decide +kernel
theorem unsat2197 : Unsatisfiable (PosFin 57) f2197 := by
  apply lratCheckerSound f2197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2197
  · intro a ha; simp [p2197] at ha; subst a; trivial
  · exact checked2197
theorem derived2197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2197 := by
  apply localUnsat_implies_entails f2197 [c2194, c2172, c2166, c2092, c2196, c38, c341, c2042, c2033, c2035, c330] c2197 unsat2197 (by rfl) a
  have h0 : Entails.eval a c2194 := derived2194 a h
  have h1 : Entails.eval a c2172 := derived2172 a h
  have h2 : Entails.eval a c2166 := derived2166 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c2196 := derived2196 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c2042 := derived2042 a h
  have h8 : Entails.eval a c2033 := derived2033 a h
  have h9 : Entails.eval a c2035 := derived2035 a h
  have h10 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2198 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2190, some c2194, some c2197, some c96, some c841, some c156, some c70, some c2092, some c2195, some c2175, some c2172, some c2166, some c2150, some c369, some c1461, some c1142, some c376, some c359, some c372, some c1129, some c283, some c363, some c191, some c373, some c1394, some c1318, some c170, some c1144, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked2198 : lratChecker f2198 p2198 = .success := by decide +kernel
theorem unsat2198 : Unsatisfiable (PosFin 57) f2198 := by
  apply lratCheckerSound f2198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2198
  · intro a ha; simp [p2198] at ha; subst a; trivial
  · exact checked2198
theorem derived2198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2198 := by
  apply localUnsat_implies_entails f2198 [c2190, c2194, c2197, c96, c841, c156, c70, c2092, c2195, c2175, c2172, c2166, c2150, c369, c1461, c1142, c376, c359, c372, c1129, c283, c363, c191, c373, c1394, c1318, c170, c1144] c2198 unsat2198 (by rfl) a
  have h0 : Entails.eval a c2190 := derived2190 a h
  have h1 : Entails.eval a c2194 := derived2194 a h
  have h2 : Entails.eval a c2197 := derived2197 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c2092 := derived2092 a h
  have h8 : Entails.eval a c2195 := derived2195 a h
  have h9 : Entails.eval a c2175 := derived2175 a h
  have h10 : Entails.eval a c2172 := derived2172 a h
  have h11 : Entails.eval a c2166 := derived2166 a h
  have h12 : Entails.eval a c2150 := derived2150 a h
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c1461 := derived1461 a h
  have h15 : Entails.eval a c1142 := derived1142 a h
  have h16 : Entails.eval a c376 := h 375 (by decide)
  have h17 : Entails.eval a c359 := h 358 (by decide)
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c1129 := derived1129 a h
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c363 := h 362 (by decide)
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c373 := h 372 (by decide)
  have h24 : Entails.eval a c1394 := derived1394 a h
  have h25 : Entails.eval a c1318 := derived1318 a h
  have h26 : Entails.eval a c170 := h 169 (by decide)
  have h27 : Entails.eval a c1144 := derived1144 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2199 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2172, some c2198, some c2032, some c2092, some c2059, some c48, some c275, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2199 : lratChecker f2199 p2199 = .success := by decide +kernel
theorem unsat2199 : Unsatisfiable (PosFin 57) f2199 := by
  apply lratCheckerSound f2199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2199
  · intro a ha; simp [p2199] at ha; subst a; trivial
  · exact checked2199
theorem derived2199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2199 := by
  apply localUnsat_implies_entails f2199 [c2172, c2198, c2032, c2092, c2059, c48, c275] c2199 unsat2199 (by rfl) a
  have h0 : Entails.eval a c2172 := derived2172 a h
  have h1 : Entails.eval a c2198 := derived2198 a h
  have h2 : Entails.eval a c2032 := derived2032 a h
  have h3 : Entails.eval a c2092 := derived2092 a h
  have h4 : Entails.eval a c2059 := derived2059 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2200 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2190, some c2194, some c2197, some c96, some c841, some c2092, some c2172, some c2198, some c2032, some c365, some c363, some c2166, some c2042, some c340, some c2199, some c300, some c193, some c248, some c250, some c1394, some c373, some c380, some c2195, some c2150, some c156, some c8, some c70, some c2175, some c169, some c1504, some c183, some c1296, some c112, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked2200 : lratChecker f2200 p2200 = .success := by decide +kernel
theorem unsat2200 : Unsatisfiable (PosFin 57) f2200 := by
  apply lratCheckerSound f2200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2200
  · intro a ha; simp [p2200] at ha; subst a; trivial
  · exact checked2200
theorem derived2200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2200 := by
  apply localUnsat_implies_entails f2200 [c2190, c2194, c2197, c96, c841, c2092, c2172, c2198, c2032, c365, c363, c2166, c2042, c340, c2199, c300, c193, c248, c250, c1394, c373, c380, c2195, c2150, c156, c8, c70, c2175, c169, c1504, c183, c1296, c112] c2200 unsat2200 (by rfl) a
  have h0 : Entails.eval a c2190 := derived2190 a h
  have h1 : Entails.eval a c2194 := derived2194 a h
  have h2 : Entails.eval a c2197 := derived2197 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c2092 := derived2092 a h
  have h6 : Entails.eval a c2172 := derived2172 a h
  have h7 : Entails.eval a c2198 := derived2198 a h
  have h8 : Entails.eval a c2032 := derived2032 a h
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c2166 := derived2166 a h
  have h12 : Entails.eval a c2042 := derived2042 a h
  have h13 : Entails.eval a c340 := h 339 (by decide)
  have h14 : Entails.eval a c2199 := derived2199 a h
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c250 := h 249 (by decide)
  have h19 : Entails.eval a c1394 := derived1394 a h
  have h20 : Entails.eval a c373 := h 372 (by decide)
  have h21 : Entails.eval a c380 := h 379 (by decide)
  have h22 : Entails.eval a c2195 := derived2195 a h
  have h23 : Entails.eval a c2150 := derived2150 a h
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c8 := h 7 (by decide)
  have h26 : Entails.eval a c70 := h 69 (by decide)
  have h27 : Entails.eval a c2175 := derived2175 a h
  have h28 : Entails.eval a c169 := h 168 (by decide)
  have h29 : Entails.eval a c1504 := derived1504 a h
  have h30 : Entails.eval a c183 := h 182 (by decide)
  have h31 : Entails.eval a c1296 := derived1296 a h
  have h32 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2201 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2092, some c2166, some c2172, some c2190, some c2194, some c2197, some c96, some c841, some c2198, some c2032, some c365, some c2042, some c363, some c340, some c2199, some c300, some c2200, some c334, some c294, some c264, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2201 : lratChecker f2201 p2201 = .success := by decide +kernel
theorem unsat2201 : Unsatisfiable (PosFin 57) f2201 := by
  apply lratCheckerSound f2201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2201
  · intro a ha; simp [p2201] at ha; subst a; trivial
  · exact checked2201
theorem derived2201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2201 := by
  apply localUnsat_implies_entails f2201 [c2092, c2166, c2172, c2190, c2194, c2197, c96, c841, c2198, c2032, c365, c2042, c363, c340, c2199, c300, c2200, c334, c294, c264] c2201 unsat2201 (by rfl) a
  have h0 : Entails.eval a c2092 := derived2092 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c2172 := derived2172 a h
  have h3 : Entails.eval a c2190 := derived2190 a h
  have h4 : Entails.eval a c2194 := derived2194 a h
  have h5 : Entails.eval a c2197 := derived2197 a h
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c2198 := derived2198 a h
  have h9 : Entails.eval a c2032 := derived2032 a h
  have h10 : Entails.eval a c365 := h 364 (by decide)
  have h11 : Entails.eval a c2042 := derived2042 a h
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c340 := h 339 (by decide)
  have h14 : Entails.eval a c2199 := derived2199 a h
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c2200 := derived2200 a h
  have h17 : Entails.eval a c334 := h 333 (by decide)
  have h18 : Entails.eval a c294 := h 293 (by decide)
  have h19 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2202 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2036, some c2022, some c2066, some c316, some c40, some c276, some c2047, some c2061, some c293, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2202 : lratChecker f2202 p2202 = .success := by decide +kernel
theorem unsat2202 : Unsatisfiable (PosFin 57) f2202 := by
  apply lratCheckerSound f2202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2202
  · intro a ha; simp [p2202] at ha; subst a; trivial
  · exact checked2202
theorem derived2202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2202 := by
  apply localUnsat_implies_entails f2202 [c2036, c2022, c2066, c316, c40, c276, c2047, c2061, c293] c2202 unsat2202 (by rfl) a
  have h0 : Entails.eval a c2036 := derived2036 a h
  have h1 : Entails.eval a c2022 := derived2022 a h
  have h2 : Entails.eval a c2066 := derived2066 a h
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c2047 := derived2047 a h
  have h7 : Entails.eval a c2061 := derived2061 a h
  have h8 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2203 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c378, some c2066, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2203 : lratChecker f2203 p2203 = .success := by decide +kernel
theorem unsat2203 : Unsatisfiable (PosFin 57) f2203 := by
  apply lratCheckerSound f2203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2203
  · intro a ha; simp [p2203] at ha; subst a; trivial
  · exact checked2203
theorem derived2203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2203 := by
  apply localUnsat_implies_entails f2203 [c374, c378, c2066] c2203 unsat2203 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c2066 := derived2066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2204 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1982, some c40, some c320, some c316, some c2050, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2204 : lratChecker f2204 p2204 = .success := by decide +kernel
theorem unsat2204 : Unsatisfiable (PosFin 57) f2204 := by
  apply lratCheckerSound f2204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2204
  · intro a ha; simp [p2204] at ha; subst a; trivial
  · exact checked2204
theorem derived2204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2204 := by
  apply localUnsat_implies_entails f2204 [c1982, c40, c320, c316, c2050] c2204 unsat2204 (by rfl) a
  have h0 : Entails.eval a c1982 := derived1982 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c2050 := derived2050 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2205 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c72, some c2093, some c91, some c2204, some c66, some c2097, some c316, some c40, some c276, some c2047, some c2061, some c293, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2205 : lratChecker f2205 p2205 = .success := by decide +kernel
theorem unsat2205 : Unsatisfiable (PosFin 57) f2205 := by
  apply lratCheckerSound f2205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2205
  · intro a ha; simp [p2205] at ha; subst a; trivial
  · exact checked2205
theorem derived2205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2205 := by
  apply localUnsat_implies_entails f2205 [c72, c2093, c91, c2204, c66, c2097, c316, c40, c276, c2047, c2061, c293] c2205 unsat2205 (by rfl) a
  have h0 : Entails.eval a c72 := h 71 (by decide)
  have h1 : Entails.eval a c2093 := derived2093 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c2204 := derived2204 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c2097 := derived2097 a h
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  have h9 : Entails.eval a c2047 := derived2047 a h
  have h10 : Entails.eval a c2061 := derived2061 a h
  have h11 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2206 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2204, some c76, some c2019, some c2040, some c316, some c2025, some c289, some c276, some c51, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2206 : lratChecker f2206 p2206 = .success := by decide +kernel
theorem unsat2206 : Unsatisfiable (PosFin 57) f2206 := by
  apply lratCheckerSound f2206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2206
  · intro a ha; simp [p2206] at ha; subst a; trivial
  · exact checked2206
theorem derived2206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2206 := by
  apply localUnsat_implies_entails f2206 [c2204, c76, c2019, c2040, c316, c2025, c289, c276, c51] c2206 unsat2206 (by rfl) a
  have h0 : Entails.eval a c2204 := derived2204 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c2019 := derived2019 a h
  have h3 : Entails.eval a c2040 := derived2040 a h
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c2025 := derived2025 a h
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2207 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c72, some c101, some c2205, some c104, some c976, some c95, some c2206, some c2068, some c1697, some c369, some c155, some c11, some c162, some c2112, some c13, some c177, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2207 : lratChecker f2207 p2207 = .success := by decide +kernel
theorem unsat2207 : Unsatisfiable (PosFin 57) f2207 := by
  apply lratCheckerSound f2207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2207
  · intro a ha; simp [p2207] at ha; subst a; trivial
  · exact checked2207
theorem derived2207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2207 := by
  apply localUnsat_implies_entails f2207 [c2201, c72, c101, c2205, c104, c976, c95, c2206, c2068, c1697, c369, c155, c11, c162, c2112, c13, c177] c2207 unsat2207 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2205 := derived2205 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c976 := derived976 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c2206 := derived2206 a h
  have h8 : Entails.eval a c2068 := derived2068 a h
  have h9 : Entails.eval a c1697 := derived1697 a h
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c2112 := derived2112 a h
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2208 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2203, some c91, some c72, some c366, some c2202, some c2204, some c168, some c66, some c2097, some c316, some c330, some c331, some c40, some c2067, some c132, some c272, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2208 : lratChecker f2208 p2208 = .success := by decide +kernel
theorem unsat2208 : Unsatisfiable (PosFin 57) f2208 := by
  apply lratCheckerSound f2208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2208
  · intro a ha; simp [p2208] at ha; subst a; trivial
  · exact checked2208
theorem derived2208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2208 := by
  apply localUnsat_implies_entails f2208 [c2203, c91, c72, c366, c2202, c2204, c168, c66, c2097, c316, c330, c331, c40, c2067, c132, c272] c2208 unsat2208 (by rfl) a
  have h0 : Entails.eval a c2203 := derived2203 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c2202 := derived2202 a h
  have h5 : Entails.eval a c2204 := derived2204 a h
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c2097 := derived2097 a h
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c330 := h 329 (by decide)
  have h11 : Entails.eval a c331 := h 330 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c2067 := derived2067 a h
  have h14 : Entails.eval a c132 := h 131 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2209 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2209 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c277, some c47, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p2209 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2209 : lratChecker f2209 p2209 = .success := by decide +kernel
theorem unsat2209 : Unsatisfiable (PosFin 57) f2209 := by
  apply lratCheckerSound f2209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2209
  · intro a ha; simp [p2209] at ha; subst a; trivial
  · exact checked2209
theorem derived2209 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2209 := by
  apply localUnsat_implies_entails f2209 [c280, c277, c47] c2209 unsat2209 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2210 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2210 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c2203, some c72, some c91, some c1636, some c380, some c1986, some c2208, some c2068, some c2027, some c2209, some c34, some c320, some c59, some c317, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2210 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2210 : lratChecker f2210 p2210 = .success := by decide +kernel
theorem unsat2210 : Unsatisfiable (PosFin 57) f2210 := by
  apply lratCheckerSound f2210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2210
  · intro a ha; simp [p2210] at ha; subst a; trivial
  · exact checked2210
theorem derived2210 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2210 := by
  apply localUnsat_implies_entails f2210 [c360, c2203, c72, c91, c1636, c380, c1986, c2208, c2068, c2027, c2209, c34, c320, c59, c317] c2210 unsat2210 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c2203 := derived2203 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c1636 := derived1636 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c1986 := derived1986 a h
  have h7 : Entails.eval a c2208 := derived2208 a h
  have h8 : Entails.eval a c2068 := derived2068 a h
  have h9 : Entails.eval a c2027 := derived2027 a h
  have h10 : Entails.eval a c2209 := derived2209 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2211 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2211 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2203, some c2207, some c152, some c360, some c1226, some c2210, some c104, some c9, some c95, some c1118, some c380, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2211 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2211 : lratChecker f2211 p2211 = .success := by decide +kernel
theorem unsat2211 : Unsatisfiable (PosFin 57) f2211 := by
  apply lratCheckerSound f2211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2211
  · intro a ha; simp [p2211] at ha; subst a; trivial
  · exact checked2211
theorem derived2211 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2211 := by
  apply localUnsat_implies_entails f2211 [c2201, c101, c2203, c2207, c152, c360, c1226, c2210, c104, c9, c95, c1118, c380] c2211 unsat2211 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2203 := derived2203 a h
  have h3 : Entails.eval a c2207 := derived2207 a h
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c1226 := derived1226 a h
  have h7 : Entails.eval a c2210 := derived2210 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c1118 := derived1118 a h
  have h12 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2212 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2212 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c1982, some c2050, some c34, some c316, some c278, some c196, some c32, some c228, some c224, some c213, some c2135, some c345, some c271, some c212, some c28, some c204, some c199, some c305, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2212 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2212 : lratChecker f2212 p2212 = .success := by decide +kernel
theorem unsat2212 : Unsatisfiable (PosFin 57) f2212 := by
  apply lratCheckerSound f2212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2212
  · intro a ha; simp [p2212] at ha; subst a; trivial
  · exact checked2212
theorem derived2212 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2212 := by
  apply localUnsat_implies_entails f2212 [c2201, c1982, c2050, c34, c316, c278, c196, c32, c228, c224, c213, c2135, c345, c271, c212, c28, c204, c199, c305] c2212 unsat2212 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c1982 := derived1982 a h
  have h2 : Entails.eval a c2050 := derived2050 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c224 := h 223 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c2135 := derived2135 a h
  have h12 : Entails.eval a c345 := h 344 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c199 := h 198 (by decide)
  have h18 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2213 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2213 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c1982, some c2212, some c320, some c318, some c196, some c269, some c32, some c228, some c224, some c278, some c201, some c2061, some c2054, some c305, some c271, some c200, some c28, some c211, some c216, some c345, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2213 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2213 : lratChecker f2213 p2213 = .success := by decide +kernel
theorem unsat2213 : Unsatisfiable (PosFin 57) f2213 := by
  apply lratCheckerSound f2213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2213
  · intro a ha; simp [p2213] at ha; subst a; trivial
  · exact checked2213
theorem derived2213 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2213 := by
  apply localUnsat_implies_entails f2213 [c2201, c1982, c2212, c320, c318, c196, c269, c32, c228, c224, c278, c201, c2061, c2054, c305, c271, c200, c28, c211, c216, c345] c2213 unsat2213 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c1982 := derived1982 a h
  have h2 : Entails.eval a c2212 := derived2212 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c224 := h 223 (by decide)
  have h10 : Entails.eval a c278 := h 277 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c2061 := derived2061 a h
  have h13 : Entails.eval a c2054 := derived2054 a h
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c271 := h 270 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c28 := h 27 (by decide)
  have h18 : Entails.eval a c211 := h 210 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2214 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨36, by decide⟩, false), (⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2214 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c2093, some c366, some c1986, some c12, some c166, some c1269, some c371, some c324, some c141, some c67, some c2026, some c35, some c316, some c293, some c298, some c2061, some c271, some c276, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2214 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2214 : lratChecker f2214 p2214 = .success := by decide +kernel
theorem unsat2214 : Unsatisfiable (PosFin 57) f2214 := by
  apply lratCheckerSound f2214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2214
  · intro a ha; simp [p2214] at ha; subst a; trivial
  · exact checked2214
theorem derived2214 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2214 := by
  apply localUnsat_implies_entails f2214 [c177, c2093, c366, c1986, c12, c166, c1269, c371, c324, c141, c67, c2026, c35, c316, c293, c298, c2061, c271, c276] c2214 unsat2214 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c2093 := derived2093 a h
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c1986 := derived1986 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c1269 := derived1269 a h
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c2026 := derived2026 a h
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c298 := h 297 (by decide)
  have h16 : Entails.eval a c2061 := derived2061 a h
  have h17 : Entails.eval a c271 := h 270 (by decide)
  have h18 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2215 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨42, by decide⟩, true), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2215 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c66, some c2093, some c366, some c2214, some c976, some c76, some c67, some c162, some c2041, some c141, some c293, some c35, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2215 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2215 : lratChecker f2215 p2215 = .success := by decide +kernel
theorem unsat2215 : Unsatisfiable (PosFin 57) f2215 := by
  apply lratCheckerSound f2215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2215
  · intro a ha; simp [p2215] at ha; subst a; trivial
  · exact checked2215
theorem derived2215 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2215 := by
  apply localUnsat_implies_entails f2215 [c177, c66, c2093, c366, c2214, c976, c76, c67, c162, c2041, c141, c293, c35] c2215 unsat2215 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c2093 := derived2093 a h
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c2214 := derived2214 a h
  have h5 : Entails.eval a c976 := derived976 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c2041 := derived2041 a h
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2216 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨36, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2216 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c269, some c284, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2216 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2216 : lratChecker f2216 p2216 = .success := by decide +kernel
theorem unsat2216 : Unsatisfiable (PosFin 57) f2216 := by
  apply lratCheckerSound f2216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2216
  · intro a ha; simp [p2216] at ha; subst a; trivial
  · exact checked2216
theorem derived2216 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2216 := by
  apply localUnsat_implies_entails f2216 [c271, c269, c284] c2216 unsat2216 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2217 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2217 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2093, some c371, some c67, some c2097, some c316, some c313, some c2216, some c276, some c2047, some c2061, some c293, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2217 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2217 : lratChecker f2217 p2217 = .success := by decide +kernel
theorem unsat2217 : Unsatisfiable (PosFin 57) f2217 := by
  apply lratCheckerSound f2217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2217
  · intro a ha; simp [p2217] at ha; subst a; trivial
  · exact checked2217
theorem derived2217 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2217 := by
  apply localUnsat_implies_entails f2217 [c2093, c371, c67, c2097, c316, c313, c2216, c276, c2047, c2061, c293] c2217 unsat2217 (by rfl) a
  have h0 : Entails.eval a c2093 := derived2093 a h
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c2097 := derived2097 a h
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c2216 := derived2216 a h
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c2047 := derived2047 a h
  have h9 : Entails.eval a c2061 := derived2061 a h
  have h10 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2218 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2218 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2211, some c101, some c2203, some c2093, some c366, some c2213, some c66, some c977, some c177, some c13, some c2215, some c2217, some c76, some c166, some c12, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2218 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2218 : lratChecker f2218 p2218 = .success := by decide +kernel
theorem unsat2218 : Unsatisfiable (PosFin 57) f2218 := by
  apply lratCheckerSound f2218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2218
  · intro a ha; simp [p2218] at ha; subst a; trivial
  · exact checked2218
theorem derived2218 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2218 := by
  apply localUnsat_implies_entails f2218 [c2211, c101, c2203, c2093, c366, c2213, c66, c977, c177, c13, c2215, c2217, c76, c166, c12] c2218 unsat2218 (by rfl) a
  have h0 : Entails.eval a c2211 := derived2211 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2203 := derived2203 a h
  have h3 : Entails.eval a c2093 := derived2093 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c2213 := derived2213 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c977 := derived977 a h
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c2215 := derived2215 a h
  have h11 : Entails.eval a c2217 := derived2217 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c166 := h 165 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2219 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2219 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2218, some c104, some c976, some c2211, some c2203, some c366, some c2213, some c977, some c177, some c13, some c9, some c162, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2219 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2219 : lratChecker f2219 p2219 = .success := by decide +kernel
theorem unsat2219 : Unsatisfiable (PosFin 57) f2219 := by
  apply lratCheckerSound f2219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2219
  · intro a ha; simp [p2219] at ha; subst a; trivial
  · exact checked2219
theorem derived2219 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2219 := by
  apply localUnsat_implies_entails f2219 [c2201, c101, c2218, c104, c976, c2211, c2203, c366, c2213, c977, c177, c13, c9, c162] c2219 unsat2219 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2218 := derived2218 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c976 := derived976 a h
  have h5 : Entails.eval a c2211 := derived2211 a h
  have h6 : Entails.eval a c2203 := derived2203 a h
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c2213 := derived2213 a h
  have h9 : Entails.eval a c977 := derived977 a h
  have h10 : Entails.eval a c177 := h 176 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2220 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2220 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c2050, some c56, some c324, some c329, some c69, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2220 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2220 : lratChecker f2220 p2220 = .success := by decide +kernel
theorem unsat2220 : Unsatisfiable (PosFin 57) f2220 := by
  apply lratCheckerSound f2220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2220
  · intro a ha; simp [p2220] at ha; subst a; trivial
  · exact checked2220
theorem derived2220 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2220 := by
  apply localUnsat_implies_entails f2220 [c318, c2050, c56, c324, c329, c69] c2220 unsat2220 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c2050 := derived2050 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2221 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2221 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c278, some c269, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p2221 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2221 : lratChecker f2221 p2221 = .success := by decide +kernel
theorem unsat2221 : Unsatisfiable (PosFin 57) f2221 := by
  apply lratCheckerSound f2221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2221
  · intro a ha; simp [p2221] at ha; subst a; trivial
  · exact checked2221
theorem derived2221 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2221 := by
  apply localUnsat_implies_entails f2221 [c280, c278, c269] c2221 unsat2221 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2222 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2222 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c104, some c2220, some c2025, some c2050, some c290, some c320, some c2221, some c44, some c289, some c1085, some c69, some c335, some c284, some c194, some c192, some c29, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2222 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2222 : lratChecker f2222 p2222 = .success := by decide +kernel
theorem unsat2222 : Unsatisfiable (PosFin 57) f2222 := by
  apply lratCheckerSound f2222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2222
  · intro a ha; simp [p2222] at ha; subst a; trivial
  · exact checked2222
theorem derived2222 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2222 := by
  apply localUnsat_implies_entails f2222 [c2201, c101, c104, c2220, c2025, c2050, c290, c320, c2221, c44, c289, c1085, c69, c335, c284, c194, c192, c29] c2222 unsat2222 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c2220 := derived2220 a h
  have h4 : Entails.eval a c2025 := derived2025 a h
  have h5 : Entails.eval a c2050 := derived2050 a h
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c2221 := derived2221 a h
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c335 := h 334 (by decide)
  have h14 : Entails.eval a c284 := h 283 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c192 := h 191 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2223 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨33, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2223 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2220, some c329, some c56, some c37, some c320, some c289, some c2221, some c2061, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2223 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2223 : lratChecker f2223 p2223 = .success := by decide +kernel
theorem unsat2223 : Unsatisfiable (PosFin 57) f2223 := by
  apply lratCheckerSound f2223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2223
  · intro a ha; simp [p2223] at ha; subst a; trivial
  · exact checked2223
theorem derived2223 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2223 := by
  apply localUnsat_implies_entails f2223 [c2220, c329, c56, c37, c320, c289, c2221, c2061] c2223 unsat2223 (by rfl) a
  have h0 : Entails.eval a c2220 := derived2220 a h
  have h1 : Entails.eval a c329 := h 328 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c2221 := derived2221 a h
  have h7 : Entails.eval a c2061 := derived2061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2224 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨38, by decide⟩, true), (⟨36, by decide⟩, true), (⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2224 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c278, some c295, some c192, some c194, some c29, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2224 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2224 : lratChecker f2224 p2224 = .success := by decide +kernel
theorem unsat2224 : Unsatisfiable (PosFin 57) f2224 := by
  apply lratCheckerSound f2224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2224
  · intro a ha; simp [p2224] at ha; subst a; trivial
  · exact checked2224
theorem derived2224 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2224 := by
  apply localUnsat_implies_entails f2224 [c278, c295, c192, c194, c29] c2224 unsat2224 (by rfl) a
  have h0 : Entails.eval a c278 := h 277 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2225 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2225 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2218, some c104, some c2219, some c2035, some c2068, some c2220, some c2222, some c330, some c2223, some c1085, some c69, some c2224, some c2061, some c44, some c290, some c284, some c194, some c192, some c29, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2225 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2225 : lratChecker f2225 p2225 = .success := by decide +kernel
theorem unsat2225 : Unsatisfiable (PosFin 57) f2225 := by
  apply lratCheckerSound f2225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2225
  · intro a ha; simp [p2225] at ha; subst a; trivial
  · exact checked2225
theorem derived2225 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2225 := by
  apply localUnsat_implies_entails f2225 [c2201, c101, c2218, c104, c2219, c2035, c2068, c2220, c2222, c330, c2223, c1085, c69, c2224, c2061, c44, c290, c284, c194, c192, c29] c2225 unsat2225 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2218 := derived2218 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c2219 := derived2219 a h
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
def c2226 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨30, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2226 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c369, some c2068, some c66, some c2094, some c371, some c67, some c2097, some c314, some c313, some c194, some c270, some c29, some c222, some c273, some c284, some c199, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2226 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2226 : lratChecker f2226 p2226 = .success := by decide +kernel
theorem unsat2226 : Unsatisfiable (PosFin 57) f2226 := by
  apply lratCheckerSound f2226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2226
  · intro a ha; simp [p2226] at ha; subst a; trivial
  · exact checked2226
theorem derived2226 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2226 := by
  apply localUnsat_implies_entails f2226 [c101, c369, c2068, c66, c2094, c371, c67, c2097, c314, c313, c194, c270, c29, c222, c273, c284, c199] c2226 unsat2226 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c2068 := derived2068 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c2097 := derived2097 a h
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c273 := h 272 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2227 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2227 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c66, some c76, some c2068, some c2041, some c293, some c325, some c324, some c266, some c56, some c333, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2227 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2227 : lratChecker f2227 p2227 = .success := by decide +kernel
theorem unsat2227 : Unsatisfiable (PosFin 57) f2227 := by
  apply lratCheckerSound f2227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2227
  · intro a ha; simp [p2227] at ha; subst a; trivial
  · exact checked2227
theorem derived2227 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2227 := by
  apply localUnsat_implies_entails f2227 [c369, c66, c76, c2068, c2041, c293, c325, c324, c266, c56, c333] c2227 unsat2227 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c2068 := derived2068 a h
  have h4 : Entails.eval a c2041 := derived2041 a h
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c325 := h 324 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2228 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2228 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2073, some c2050, some c826, some c335, some c194, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2228 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2228 : lratChecker f2228 p2228 = .success := by decide +kernel
theorem unsat2228 : Unsatisfiable (PosFin 57) f2228 := by
  apply lratCheckerSound f2228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2228
  · intro a ha; simp [p2228] at ha; subst a; trivial
  · exact checked2228
theorem derived2228 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2228 := by
  apply localUnsat_implies_entails f2228 [c101, c2073, c2050, c826, c335, c194] c2228 unsat2228 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2073 := derived2073 a h
  have h2 : Entails.eval a c2050 := derived2050 a h
  have h3 : Entails.eval a c826 := derived826 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2229 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2229 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2203, some c2225, some c1241, some c1051, some c155, some c168, some c369, some c66, some c2068, some c2073, some c2226, some c104, some c976, some c76, some c2041, some c359, some c293, some c2227, some c2228, some c314, some c313, some c266, some c56, some c333, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2229 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked2229 : lratChecker f2229 p2229 = .success := by decide +kernel
theorem unsat2229 : Unsatisfiable (PosFin 57) f2229 := by
  apply lratCheckerSound f2229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2229
  · intro a ha; simp [p2229] at ha; subst a; trivial
  · exact checked2229
theorem derived2229 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2229 := by
  apply localUnsat_implies_entails f2229 [c2201, c101, c2203, c2225, c1241, c1051, c155, c168, c369, c66, c2068, c2073, c2226, c104, c976, c76, c2041, c359, c293, c2227, c2228, c314, c313, c266, c56, c333] c2229 unsat2229 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2203 := derived2203 a h
  have h3 : Entails.eval a c2225 := derived2225 a h
  have h4 : Entails.eval a c1241 := derived1241 a h
  have h5 : Entails.eval a c1051 := derived1051 a h
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c2068 := derived2068 a h
  have h11 : Entails.eval a c2073 := derived2073 a h
  have h12 : Entails.eval a c2226 := derived2226 a h
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c976 := derived976 a h
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c2041 := derived2041 a h
  have h17 : Entails.eval a c359 := h 358 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c2227 := derived2227 a h
  have h20 : Entails.eval a c2228 := derived2228 a h
  have h21 : Entails.eval a c314 := h 313 (by decide)
  have h22 : Entails.eval a c313 := h 312 (by decide)
  have h23 : Entails.eval a c266 := h 265 (by decide)
  have h24 : Entails.eval a c56 := h 55 (by decide)
  have h25 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2230 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2230 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c380, some c2036, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p2230 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2230 : lratChecker f2230 p2230 = .success := by decide +kernel
theorem unsat2230 : Unsatisfiable (PosFin 57) f2230 := by
  apply lratCheckerSound f2230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2230
  · intro a ha; simp [p2230] at ha; subst a; trivial
  · exact checked2230
theorem derived2230 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2230 := by
  apply localUnsat_implies_entails f2230 [c373, c380, c2036] c2230 unsat2230 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c2036 := derived2036 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2231 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2231 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c360, some c2230, some c361, some c366, some c168, some c16, some c1986, some c179, some c2008, some c69, some c1491, some c2041, some c1118, some c293, some c2097, some c35, some c313, some c333, some c56, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2231 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2231 : lratChecker f2231 p2231 = .success := by decide +kernel
theorem unsat2231 : Unsatisfiable (PosFin 57) f2231 := by
  apply lratCheckerSound f2231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2231
  · intro a ha; simp [p2231] at ha; subst a; trivial
  · exact checked2231
theorem derived2231 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2231 := by
  apply localUnsat_implies_entails f2231 [c2201, c360, c2230, c361, c366, c168, c16, c1986, c179, c2008, c69, c1491, c2041, c1118, c293, c2097, c35, c313, c333, c56] c2231 unsat2231 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c2230 := derived2230 a h
  have h3 : Entails.eval a c361 := h 360 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c1986 := derived1986 a h
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c2008 := derived2008 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c1491 := derived1491 a h
  have h12 : Entails.eval a c2041 := derived2041 a h
  have h13 : Entails.eval a c1118 := derived1118 a h
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c2097 := derived2097 a h
  have h16 : Entails.eval a c35 := h 34 (by decide)
  have h17 : Entails.eval a c313 := h 312 (by decide)
  have h18 : Entails.eval a c333 := h 332 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2232 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2232 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c361, some c360, some c2230, some c2231, some c2068, some c2027, some c370, some c168, some c16, some c1986, some c69, some c2065, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2232 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2232 : lratChecker f2232 p2232 = .success := by decide +kernel
theorem unsat2232 : Unsatisfiable (PosFin 57) f2232 := by
  apply lratCheckerSound f2232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2232
  · intro a ha; simp [p2232] at ha; subst a; trivial
  · exact checked2232
theorem derived2232 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2232 := by
  apply localUnsat_implies_entails f2232 [c2201, c361, c360, c2230, c2231, c2068, c2027, c370, c168, c16, c1986, c69, c2065] c2232 unsat2232 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c2230 := derived2230 a h
  have h4 : Entails.eval a c2231 := derived2231 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c2027 := derived2027 a h
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c1986 := derived1986 a h
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c2065 := derived2065 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2233 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2233 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c295, some c335, some c333, some c266, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p2233 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2233 : lratChecker f2233 p2233 = .success := by decide +kernel
theorem unsat2233 : Unsatisfiable (PosFin 57) f2233 := by
  apply lratCheckerSound f2233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2233
  · intro a ha; simp [p2233] at ha; subst a; trivial
  · exact checked2233
theorem derived2233 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2233 := by
  apply localUnsat_implies_entails f2233 [c293, c295, c335, c333, c266] c2233 unsat2233 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2234 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2234 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2041, some c2233, some c2050, some c56, some c313, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2234 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2234 : lratChecker f2234 p2234 = .success := by decide +kernel
theorem unsat2234 : Unsatisfiable (PosFin 57) f2234 := by
  apply lratCheckerSound f2234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2234
  · intro a ha; simp [p2234] at ha; subst a; trivial
  · exact checked2234
theorem derived2234 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2234 := by
  apply localUnsat_implies_entails f2234 [c2041, c2233, c2050, c56, c313] c2234 unsat2234 (by rfl) a
  have h0 : Entails.eval a c2041 := derived2041 a h
  have h1 : Entails.eval a c2233 := derived2233 a h
  have h2 : Entails.eval a c2050 := derived2050 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2235 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2235 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2203, some c2211, some c2229, some c152, some c360, some c1226, some c361, some c2232, some c104, some c9, some c2008, some c1118, some c380, some c69, some c2234, some c2068, some c370, some c2065, some c162, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2235 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2235 : lratChecker f2235 p2235 = .success := by decide +kernel
theorem unsat2235 : Unsatisfiable (PosFin 57) f2235 := by
  apply lratCheckerSound f2235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2235
  · intro a ha; simp [p2235] at ha; subst a; trivial
  · exact checked2235
theorem derived2235 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2235 := by
  apply localUnsat_implies_entails f2235 [c2201, c101, c2203, c2211, c2229, c152, c360, c1226, c361, c2232, c104, c9, c2008, c1118, c380, c69, c2234, c2068, c370, c2065, c162] c2235 unsat2235 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2203 := derived2203 a h
  have h3 : Entails.eval a c2211 := derived2211 a h
  have h4 : Entails.eval a c2229 := derived2229 a h
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c1226 := derived1226 a h
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c2232 := derived2232 a h
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c2008 := derived2008 a h
  have h13 : Entails.eval a c1118 := derived1118 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c2234 := derived2234 a h
  have h17 : Entails.eval a c2068 := derived2068 a h
  have h18 : Entails.eval a c370 := h 369 (by decide)
  have h19 : Entails.eval a c2065 := derived2065 a h
  have h20 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2236 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨5, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2236 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2235, some c101, some c364, some c154, some c841, some c2230, some c2205, some c1986, some c15, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2236 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2236 : lratChecker f2236 p2236 = .success := by decide +kernel
theorem unsat2236 : Unsatisfiable (PosFin 57) f2236 := by
  apply lratCheckerSound f2236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2236
  · intro a ha; simp [p2236] at ha; subst a; trivial
  · exact checked2236
theorem derived2236 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2236 := by
  apply localUnsat_implies_entails f2236 [c2235, c101, c364, c154, c841, c2230, c2205, c1986, c15] c2236 unsat2236 (by rfl) a
  have h0 : Entails.eval a c2235 := derived2235 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c364 := h 363 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c2230 := derived2230 a h
  have h6 : Entails.eval a c2205 := derived2205 a h
  have h7 : Entails.eval a c1986 := derived1986 a h
  have h8 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2237 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2237 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c369, some c66, some c2093, some c366, some c2226, some c2094, some c274, some c371, some c2047, some c2061, some c67, some c293, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2237 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2237 : lratChecker f2237 p2237 = .success := by decide +kernel
theorem unsat2237 : Unsatisfiable (PosFin 57) f2237 := by
  apply lratCheckerSound f2237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2237
  · intro a ha; simp [p2237] at ha; subst a; trivial
  · exact checked2237
theorem derived2237 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2237 := by
  apply localUnsat_implies_entails f2237 [c101, c369, c66, c2093, c366, c2226, c2094, c274, c371, c2047, c2061, c67, c293] c2237 unsat2237 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c2093 := derived2093 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c2226 := derived2226 a h
  have h6 : Entails.eval a c2094 := derived2094 a h
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c2047 := derived2047 a h
  have h10 : Entails.eval a c2061 := derived2061 a h
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2238 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2238 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c273, some c270, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2238 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2238 : lratChecker f2238 p2238 = .success := by decide +kernel
theorem unsat2238 : Unsatisfiable (PosFin 57) f2238 := by
  apply lratCheckerSound f2238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2238
  · intro a ha; simp [p2238] at ha; subst a; trivial
  · exact checked2238
theorem derived2238 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2238 := by
  apply localUnsat_implies_entails f2238 [c274, c273, c270] c2238 unsat2238 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2239 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨51, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2239 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c296, some c293, some c47, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2239 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2239 : lratChecker f2239 p2239 = .success := by decide +kernel
theorem unsat2239 : Unsatisfiable (PosFin 57) f2239 := by
  apply lratCheckerSound f2239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2239
  · intro a ha; simp [p2239] at ha; subst a; trivial
  · exact checked2239
theorem derived2239 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2239 := by
  apply localUnsat_implies_entails f2239 [c296, c293, c47] c2239 unsat2239 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2240 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2240 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2239, some c34, some c336, some c333, some c59, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2240 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2240 : lratChecker f2240 p2240 = .success := by decide +kernel
theorem unsat2240 : Unsatisfiable (PosFin 57) f2240 := by
  apply lratCheckerSound f2240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2240
  · intro a ha; simp [p2240] at ha; subst a; trivial
  · exact checked2240
theorem derived2240 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2240 := by
  apply localUnsat_implies_entails f2240 [c2239, c34, c336, c333, c59] c2240 unsat2240 (by rfl) a
  have h0 : Entails.eval a c2239 := derived2239 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2241 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨2, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2241 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2240, some c2036, some c2136, some c40, some c336, some c332, some c2050, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2241 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2241 : lratChecker f2241 p2241 = .success := by decide +kernel
theorem unsat2241 : Unsatisfiable (PosFin 57) f2241 := by
  apply lratCheckerSound f2241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2241
  · intro a ha; simp [p2241] at ha; subst a; trivial
  · exact checked2241
theorem derived2241 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2241 := by
  apply localUnsat_implies_entails f2241 [c2240, c2036, c2136, c40, c336, c332, c2050] c2241 unsat2241 (by rfl) a
  have h0 : Entails.eval a c2240 := derived2240 a h
  have h1 : Entails.eval a c2036 := derived2036 a h
  have h2 : Entails.eval a c2136 := derived2136 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c336 := h 335 (by decide)
  have h5 : Entails.eval a c332 := h 331 (by decide)
  have h6 : Entails.eval a c2050 := derived2050 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2242 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2242 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2093, some c2236, some c369, some c366, some c66, some c2237, some c155, some c1051, some c14, some c2241, some c16, some c167, some c371, some c67, some c2097, some c314, some c313, some c2238, some c2047, some c2061, some c293, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2242 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2242 : lratChecker f2242 p2242 = .success := by decide +kernel
theorem unsat2242 : Unsatisfiable (PosFin 57) f2242 := by
  apply lratCheckerSound f2242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2242
  · intro a ha; simp [p2242] at ha; subst a; trivial
  · exact checked2242
theorem derived2242 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2242 := by
  apply localUnsat_implies_entails f2242 [c2201, c101, c2093, c2236, c369, c366, c66, c2237, c155, c1051, c14, c2241, c16, c167, c371, c67, c2097, c314, c313, c2238, c2047, c2061, c293] c2242 unsat2242 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2093 := derived2093 a h
  have h3 : Entails.eval a c2236 := derived2236 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c2237 := derived2237 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c1051 := derived1051 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c2241 := derived2241 a h
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c167 := h 166 (by decide)
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c67 := h 66 (by decide)
  have h16 : Entails.eval a c2097 := derived2097 a h
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c2238 := derived2238 a h
  have h20 : Entails.eval a c2047 := derived2047 a h
  have h21 : Entails.eval a c2061 := derived2061 a h
  have h22 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2243 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2243 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2235, some c101, some c364, some c154, some c841, some c13, some c2205, some c177, some c15, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2243 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2243 : lratChecker f2243 p2243 = .success := by decide +kernel
theorem unsat2243 : Unsatisfiable (PosFin 57) f2243 := by
  apply lratCheckerSound f2243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2243
  · intro a ha; simp [p2243] at ha; subst a; trivial
  · exact checked2243
theorem derived2243 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2243 := by
  apply localUnsat_implies_entails f2243 [c2235, c101, c364, c154, c841, c13, c2205, c177, c15] c2243 unsat2243 (by rfl) a
  have h0 : Entails.eval a c2235 := derived2235 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c364 := h 363 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c2205 := derived2205 a h
  have h7 : Entails.eval a c177 := h 176 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2244 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2244 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2093, some c2242, some c976, some c67, some c2243, some c369, some c66, some c76, some c2097, some c2041, some c314, some c313, some c293, some c2238, some c2047, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2244 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2244 : lratChecker f2244 p2244 = .success := by decide +kernel
theorem unsat2244 : Unsatisfiable (PosFin 57) f2244 := by
  apply lratCheckerSound f2244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2244
  · intro a ha; simp [p2244] at ha; subst a; trivial
  · exact checked2244
theorem derived2244 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2244 := by
  apply localUnsat_implies_entails f2244 [c101, c2093, c2242, c976, c67, c2243, c369, c66, c76, c2097, c2041, c314, c313, c293, c2238, c2047] c2244 unsat2244 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2093 := derived2093 a h
  have h2 : Entails.eval a c2242 := derived2242 a h
  have h3 : Entails.eval a c976 := derived976 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c2243 := derived2243 a h
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c2097 := derived2097 a h
  have h10 : Entails.eval a c2041 := derived2041 a h
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c2238 := derived2238 a h
  have h15 : Entails.eval a c2047 := derived2047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2245 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2245 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2235, some c101, some c2244, some c152, some c360, some c1226, some c841, some c2230, some c2232, some c178, some c1636, some c12, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2245 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2245 : lratChecker f2245 p2245 = .success := by decide +kernel
theorem unsat2245 : Unsatisfiable (PosFin 57) f2245 := by
  apply lratCheckerSound f2245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2245
  · intro a ha; simp [p2245] at ha; subst a; trivial
  · exact checked2245
theorem derived2245 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2245 := by
  apply localUnsat_implies_entails f2245 [c2235, c101, c2244, c152, c360, c1226, c841, c2230, c2232, c178, c1636, c12] c2245 unsat2245 (by rfl) a
  have h0 : Entails.eval a c2235 := derived2235 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2244 := derived2244 a h
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c1226 := derived1226 a h
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c2230 := derived2230 a h
  have h8 : Entails.eval a c2232 := derived2232 a h
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c1636 := derived1636 a h
  have h11 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2246 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2246 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2235, some c364, some c154, some c841, some c13, some c2207, some c177, some c15, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2246 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2246 : lratChecker f2246 p2246 = .success := by decide +kernel
theorem unsat2246 : Unsatisfiable (PosFin 57) f2246 := by
  apply lratCheckerSound f2246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2246
  · intro a ha; simp [p2246] at ha; subst a; trivial
  · exact checked2246
theorem derived2246 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2246 := by
  apply localUnsat_implies_entails f2246 [c2235, c364, c154, c841, c13, c2207, c177, c15] c2246 unsat2246 (by rfl) a
  have h0 : Entails.eval a c2235 := derived2235 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c2207 := derived2207 a h
  have h6 : Entails.eval a c177 := h 176 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2247 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2247 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c140, some c267, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p2247 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2247 : lratChecker f2247 p2247 = .success := by decide +kernel
theorem unsat2247 : Unsatisfiable (PosFin 57) f2247 := by
  apply lratCheckerSound f2247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2247
  · intro a ha; simp [p2247] at ha; subst a; trivial
  · exact checked2247
theorem derived2247 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2247 := by
  apply localUnsat_implies_entails f2247 [c333, c140, c267] c2247 unsat2247 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2248 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2248 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2050, some c56, some c313, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2248 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2248 : lratChecker f2248 p2248 = .success := by decide +kernel
theorem unsat2248 : Unsatisfiable (PosFin 57) f2248 := by
  apply lratCheckerSound f2248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2248
  · intro a ha; simp [p2248] at ha; subst a; trivial
  · exact checked2248
theorem derived2248 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2248 := by
  apply localUnsat_implies_entails f2248 [c2050, c56, c313] c2248 unsat2248 (by rfl) a
  have h0 : Entails.eval a c2050 := derived2050 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2249 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨48, by decide⟩, true), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨43, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2249 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c156, some c1051, some c359, some c161, some c293, some c124, some c2247, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p2249 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2249 : lratChecker f2249 p2249 = .success := by decide +kernel
theorem unsat2249 : Unsatisfiable (PosFin 57) f2249 := by
  apply lratCheckerSound f2249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2249
  · intro a ha; simp [p2249] at ha; subst a; trivial
  · exact checked2249
theorem derived2249 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2249 := by
  apply localUnsat_implies_entails f2249 [c2201, c156, c1051, c359, c161, c293, c124, c2247] c2249 unsat2249 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c1051 := derived1051 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c2247 := derived2247 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2250 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2250 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c104, some c76, some c66, some c366, some c2041, some c2248, some c2249, some c841, some c296, some c336, some c155, some c947, some c267, some c11, some c333, some c1118, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2250 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2250 : lratChecker f2250 p2250 = .success := by decide +kernel
theorem unsat2250 : Unsatisfiable (PosFin 57) f2250 := by
  apply lratCheckerSound f2250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2250
  · intro a ha; simp [p2250] at ha; subst a; trivial
  · exact checked2250
theorem derived2250 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2250 := by
  apply localUnsat_implies_entails f2250 [c2201, c104, c76, c66, c366, c2041, c2248, c2249, c841, c296, c336, c155, c947, c267, c11, c333, c1118] c2250 unsat2250 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c2041 := derived2041 a h
  have h6 : Entails.eval a c2248 := derived2248 a h
  have h7 : Entails.eval a c2249 := derived2249 a h
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c336 := h 335 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c947 := derived947 a h
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c1118 := derived1118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2251 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2251 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2250, some c2068, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p2251 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2251 : lratChecker f2251 p2251 = .success := by decide +kernel
theorem unsat2251 : Unsatisfiable (PosFin 57) f2251 := by
  apply lratCheckerSound f2251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2251
  · intro a ha; simp [p2251] at ha; subst a; trivial
  · exact checked2251
theorem derived2251 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2251 := by
  apply localUnsat_implies_entails f2251 [c2250, c2068] c2251 unsat2251 (by rfl) a
  have h0 : Entails.eval a c2250 := derived2250 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2252 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2252 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2245, some c104, some c101, some c976, some c2246, some c369, some c2251, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2252 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2252 : lratChecker f2252 p2252 = .success := by decide +kernel
theorem unsat2252 : Unsatisfiable (PosFin 57) f2252 := by
  apply lratCheckerSound f2252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2252
  · intro a ha; simp [p2252] at ha; subst a; trivial
  · exact checked2252
theorem derived2252 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2252 := by
  apply localUnsat_implies_entails f2252 [c2201, c2245, c104, c101, c976, c2246, c369, c2251] c2252 unsat2252 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2245 := derived2245 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c976 := derived976 a h
  have h5 : Entails.eval a c2246 := derived2246 a h
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c2251 := derived2251 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2253 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2253 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2235, some c2252, some c360, some c1226, some c841, some c154, some c361, some c370, some c366, some c2068, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2253 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2253 : lratChecker f2253 p2253 = .success := by decide +kernel
theorem unsat2253 : Unsatisfiable (PosFin 57) f2253 := by
  apply lratCheckerSound f2253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2253
  · intro a ha; simp [p2253] at ha; subst a; trivial
  · exact checked2253
theorem derived2253 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2253 := by
  apply localUnsat_implies_entails f2253 [c101, c2235, c2252, c360, c1226, c841, c154, c361, c370, c366, c2068] c2253 unsat2253 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2235 := derived2235 a h
  have h2 : Entails.eval a c2252 := derived2252 a h
  have h3 : Entails.eval a c360 := h 359 (by decide)
  have h4 : Entails.eval a c1226 := derived1226 a h
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c2068 := derived2068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2254 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2254 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2204, some c2213, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2254 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2254 : lratChecker f2254 p2254 = .success := by decide +kernel
theorem unsat2254 : Unsatisfiable (PosFin 57) f2254 := by
  apply lratCheckerSound f2254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2254
  · intro a ha; simp [p2254] at ha; subst a; trivial
  · exact checked2254
theorem derived2254 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2254 := by
  apply localUnsat_implies_entails f2254 [c2204, c2213] c2254 unsat2254 (by rfl) a
  have h0 : Entails.eval a c2204 := derived2204 a h
  have h1 : Entails.eval a c2213 := derived2213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2255 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2255 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c377, some c67, some c2036, some c364, some c371, some c373, some c362, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p2255 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2255 : lratChecker f2255 p2255 = .success := by decide +kernel
theorem unsat2255 : Unsatisfiable (PosFin 57) f2255 := by
  apply lratCheckerSound f2255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2255
  · intro a ha; simp [p2255] at ha; subst a; trivial
  · exact checked2255
theorem derived2255 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2255 := by
  apply localUnsat_implies_entails f2255 [c376, c377, c67, c2036, c364, c371, c373, c362] c2255 unsat2255 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c2036 := derived2036 a h
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2256 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2256 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2253, some c101, some c2255, some c2066, some c66, some c1039, some c2254, some c1241, some c1051, some c168, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2256 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2256 : lratChecker f2256 p2256 = .success := by decide +kernel
theorem unsat2256 : Unsatisfiable (PosFin 57) f2256 := by
  apply lratCheckerSound f2256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2256
  · intro a ha; simp [p2256] at ha; subst a; trivial
  · exact checked2256
theorem derived2256 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2256 := by
  apply localUnsat_implies_entails f2256 [c2201, c2253, c101, c2255, c2066, c66, c1039, c2254, c1241, c1051, c168] c2256 unsat2256 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2255 := derived2255 a h
  have h4 : Entails.eval a c2066 := derived2066 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c1039 := derived1039 a h
  have h7 : Entails.eval a c2254 := derived2254 a h
  have h8 : Entails.eval a c1241 := derived1241 a h
  have h9 : Entails.eval a c1051 := derived1051 a h
  have h10 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2257 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2257 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2253, some c101, some c2256, some c369, some c2237, some c366, some c66, some c155, some c376, some c1051, some c1118, some c67, some c2241, some c188, some c371, some c16, some c167, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2257 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2257 : lratChecker f2257 p2257 = .success := by decide +kernel
theorem unsat2257 : Unsatisfiable (PosFin 57) f2257 := by
  apply lratCheckerSound f2257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2257
  · intro a ha; simp [p2257] at ha; subst a; trivial
  · exact checked2257
theorem derived2257 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2257 := by
  apply localUnsat_implies_entails f2257 [c2201, c2253, c101, c2256, c369, c2237, c366, c66, c155, c376, c1051, c1118, c67, c2241, c188, c371, c16, c167] c2257 unsat2257 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2256 := derived2256 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c2237 := derived2237 a h
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c1051 := derived1051 a h
  have h11 : Entails.eval a c1118 := derived1118 a h
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c2241 := derived2241 a h
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c16 := h 15 (by decide)
  have h17 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2258 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2258 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2253, some c101, some c2257, some c104, some c968, some c976, some c1118, some c11, some c155, some c841, some c2008, some c359, some c377, some c366, some c358, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2258 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2258 : lratChecker f2258 p2258 = .success := by decide +kernel
theorem unsat2258 : Unsatisfiable (PosFin 57) f2258 := by
  apply lratCheckerSound f2258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2258
  · intro a ha; simp [p2258] at ha; subst a; trivial
  · exact checked2258
theorem derived2258 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2258 := by
  apply localUnsat_implies_entails f2258 [c2201, c2253, c101, c2257, c104, c968, c976, c1118, c11, c155, c841, c2008, c359, c377, c366, c358] c2258 unsat2258 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2257 := derived2257 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c968 := derived968 a h
  have h6 : Entails.eval a c976 := derived976 a h
  have h7 : Entails.eval a c1118 := derived1118 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c2008 := derived2008 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2259 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2259 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2253, some c101, some c2258, some c2035, some c2068, some c2093, some c369, some c368, some c104, some c1039, some c968, some c359, some c956, some c358, some c1085, some c2222, some c2223, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2259 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2259 : lratChecker f2259 p2259 = .success := by decide +kernel
theorem unsat2259 : Unsatisfiable (PosFin 57) f2259 := by
  apply lratCheckerSound f2259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2259
  · intro a ha; simp [p2259] at ha; subst a; trivial
  · exact checked2259
theorem derived2259 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2259 := by
  apply localUnsat_implies_entails f2259 [c2201, c2253, c101, c2258, c2035, c2068, c2093, c369, c368, c104, c1039, c968, c359, c956, c358, c1085, c2222, c2223] c2259 unsat2259 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c2258 := derived2258 a h
  have h4 : Entails.eval a c2035 := derived2035 a h
  have h5 : Entails.eval a c2068 := derived2068 a h
  have h6 : Entails.eval a c2093 := derived2093 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c1039 := derived1039 a h
  have h11 : Entails.eval a c968 := derived968 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c956 := derived956 a h
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c1085 := derived1085 a h
  have h16 : Entails.eval a c2222 := derived2222 a h
  have h17 : Entails.eval a c2223 := derived2223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2260 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2260 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c12, some c14, some c164, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2260 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2260 : lratChecker f2260 p2260 = .success := by decide +kernel
theorem unsat2260 : Unsatisfiable (PosFin 57) f2260 := by
  apply lratCheckerSound f2260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2260
  · intro a ha; simp [p2260] at ha; subst a; trivial
  · exact checked2260
theorem derived2260 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2260 := by
  apply localUnsat_implies_entails f2260 [c2201, c12, c14, c164] c2260 unsat2260 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2261 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2261 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c16, some c15, some c168, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p2261 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2261 : lratChecker f2261 p2261 = .success := by decide +kernel
theorem unsat2261 : Unsatisfiable (PosFin 57) f2261 := by
  apply lratCheckerSound f2261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2261
  · intro a ha; simp [p2261] at ha; subst a; trivial
  · exact checked2261
theorem derived2261 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2261 := by
  apply localUnsat_implies_entails f2261 [c2201, c16, c15, c168] c2261 unsat2261 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2262 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨56, by decide⟩, true), (⟨16, by decide⟩, true), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2262 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c968, some c179, some c2260, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2262 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2262 : lratChecker f2262 p2262 = .success := by decide +kernel
theorem unsat2262 : Unsatisfiable (PosFin 57) f2262 := by
  apply lratCheckerSound f2262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2262
  · intro a ha; simp [p2262] at ha; subst a; trivial
  · exact checked2262
theorem derived2262 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2262 := by
  apply localUnsat_implies_entails f2262 [c379, c968, c179, c2260] c2262 unsat2262 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c2260 := derived2260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2263 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨15, by decide⟩, false), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2263 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2047, some c35, some c290, some c289, some c317, some c143, some c1265, some c864, some c2050, some c398, some c330, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2263 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2263 : lratChecker f2263 p2263 = .success := by decide +kernel
theorem unsat2263 : Unsatisfiable (PosFin 57) f2263 := by
  apply lratCheckerSound f2263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2263
  · intro a ha; simp [p2263] at ha; subst a; trivial
  · exact checked2263
theorem derived2263 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2263 := by
  apply localUnsat_implies_entails f2263 [c2201, c2047, c35, c290, c289, c317, c143, c1265, c864, c2050, c398, c330] c2263 unsat2263 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2047 := derived2047 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c1265 := derived1265 a h
  have h8 : Entails.eval a c864 := derived864 a h
  have h9 : Entails.eval a c2050 := derived2050 a h
  have h10 : Entails.eval a c398 := derived398 a h
  have h11 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2264 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨15, by decide⟩, false), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2264 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2263, some c277, some c127, some c2061, some c34, some c289, some c320, some c864, some c196, some c201, some c228, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2264 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2264 : lratChecker f2264 p2264 = .success := by decide +kernel
theorem unsat2264 : Unsatisfiable (PosFin 57) f2264 := by
  apply lratCheckerSound f2264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2264
  · intro a ha; simp [p2264] at ha; subst a; trivial
  · exact checked2264
theorem derived2264 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2264 := by
  apply localUnsat_implies_entails f2264 [c2201, c2263, c277, c127, c2061, c34, c289, c320, c864, c196, c201, c228] c2264 unsat2264 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2263 := derived2263 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c2061 := derived2061 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c864 := derived864 a h
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2265 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨5, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2265 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2050, some c56, some c329, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2265 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2265 : lratChecker f2265 p2265 = .success := by decide +kernel
theorem unsat2265 : Unsatisfiable (PosFin 57) f2265 := by
  apply lratCheckerSound f2265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2265
  · intro a ha; simp [p2265] at ha; subst a; trivial
  · exact checked2265
theorem derived2265 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2265 := by
  apply localUnsat_implies_entails f2265 [c2050, c56, c329] c2265 unsat2265 (by rfl) a
  have h0 : Entails.eval a c2050 := derived2050 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2266 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2266 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c2264, some c2265, some c320, some c317, some c196, some c2046, some c32, some c228, some c277, some c127, some c201, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p2266 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2266 : lratChecker f2266 p2266 = .success := by decide +kernel
theorem unsat2266 : Unsatisfiable (PosFin 57) f2266 := by
  apply lratCheckerSound f2266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2266
  · intro a ha; simp [p2266] at ha; subst a; trivial
  · exact checked2266
theorem derived2266 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2266 := by
  apply localUnsat_implies_entails f2266 [c2201, c2264, c2265, c320, c317, c196, c2046, c32, c228, c277, c127, c201] c2266 unsat2266 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c2264 := derived2264 a h
  have h2 : Entails.eval a c2265 := derived2265 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c2046 := derived2046 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c277 := h 276 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2267 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2267 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1039, some c2262, some c1118, some c67, some c1491, some c179, some c373, some c155, some c364, some c2266, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2267 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2267 : lratChecker f2267 p2267 = .success := by decide +kernel
theorem unsat2267 : Unsatisfiable (PosFin 57) f2267 := by
  apply lratCheckerSound f2267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2267
  · intro a ha; simp [p2267] at ha; subst a; trivial
  · exact checked2267
theorem derived2267 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2267 := by
  apply localUnsat_implies_entails f2267 [c1039, c2262, c1118, c67, c1491, c179, c373, c155, c364, c2266] c2267 unsat2267 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c2262 := derived2262 a h
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c1491 := derived1491 a h
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  have h7 : Entails.eval a c155 := h 154 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c2266 := derived2266 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2268 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2268 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2066, some c2036, some c376, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2268 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2268 : lratChecker f2268 p2268 = .success := by decide +kernel
theorem unsat2268 : Unsatisfiable (PosFin 57) f2268 := by
  apply lratCheckerSound f2268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2268
  · intro a ha; simp [p2268] at ha; subst a; trivial
  · exact checked2268
theorem derived2268 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2268 := by
  apply localUnsat_implies_entails f2268 [c2066, c2036, c376] c2268 unsat2268 (by rfl) a
  have h0 : Entails.eval a c2066 := derived2066 a h
  have h1 : Entails.eval a c2036 := derived2036 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2269 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2269 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c2253, some c2268, some c2259, some c1982, some c2204, some c2261, some c2267, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2269 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2269 : lratChecker f2269 p2269 = .success := by decide +kernel
theorem unsat2269 : Unsatisfiable (PosFin 57) f2269 := by
  apply lratCheckerSound f2269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2269
  · intro a ha; simp [p2269] at ha; subst a; trivial
  · exact checked2269
theorem derived2269 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2269 := by
  apply localUnsat_implies_entails f2269 [c101, c2253, c2268, c2259, c1982, c2204, c2261, c2267] c2269 unsat2269 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c2268 := derived2268 a h
  have h3 : Entails.eval a c2259 := derived2259 a h
  have h4 : Entails.eval a c1982 := derived1982 a h
  have h5 : Entails.eval a c2204 := derived2204 a h
  have h6 : Entails.eval a c2261 := derived2261 a h
  have h7 : Entails.eval a c2267 := derived2267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2270 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2270 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1039, some c376, some c377, some c1118, some c67, some c1040, some c364, some c1491, some c2230, some c179, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p2270 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2270 : lratChecker f2270 p2270 = .success := by decide +kernel
theorem unsat2270 : Unsatisfiable (PosFin 57) f2270 := by
  apply lratCheckerSound f2270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2270
  · intro a ha; simp [p2270] at ha; subst a; trivial
  · exact checked2270
theorem derived2270 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2270 := by
  apply localUnsat_implies_entails f2270 [c1039, c376, c377, c1118, c67, c1040, c364, c1491, c2230, c179] c2270 unsat2270 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c1040 := derived1040 a h
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c1491 := derived1491 a h
  have h8 : Entails.eval a c2230 := derived2230 a h
  have h9 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2271 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2271 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2253, some c2268, some c2259, some c1039, some c2270, some c66, some c2269, some c1241, some c1051, some c168, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2271 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2271 : lratChecker f2271 p2271 = .success := by decide +kernel
theorem unsat2271 : Unsatisfiable (PosFin 57) f2271 := by
  apply lratCheckerSound f2271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2271
  · intro a ha; simp [p2271] at ha; subst a; trivial
  · exact checked2271
theorem derived2271 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2271 := by
  apply localUnsat_implies_entails f2271 [c2201, c101, c2253, c2268, c2259, c1039, c2270, c66, c2269, c1241, c1051, c168] c2271 unsat2271 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2253 := derived2253 a h
  have h3 : Entails.eval a c2268 := derived2268 a h
  have h4 : Entails.eval a c2259 := derived2259 a h
  have h5 : Entails.eval a c1039 := derived1039 a h
  have h6 : Entails.eval a c2270 := derived2270 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c2269 := derived2269 a h
  have h9 : Entails.eval a c1241 := derived1241 a h
  have h10 : Entails.eval a c1051 := derived1051 a h
  have h11 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2272 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨55, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2272 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c331, some c272, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p2272 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2272 : lratChecker f2272 p2272 = .success := by decide +kernel
theorem unsat2272 : Unsatisfiable (PosFin 57) f2272 := by
  apply lratCheckerSound f2272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2272
  · intro a ha; simp [p2272] at ha; subst a; trivial
  · exact checked2272
theorem derived2272 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2272 := by
  apply localUnsat_implies_entails f2272 [c314, c331, c272] c2272 unsat2272 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c331 := h 330 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2273 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2273 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c279, some c274, some c2061, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2273 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2273 : lratChecker f2273 p2273 = .success := by decide +kernel
theorem unsat2273 : Unsatisfiable (PosFin 57) f2273 := by
  apply lratCheckerSound f2273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2273
  · intro a ha; simp [p2273] at ha; subst a; trivial
  · exact checked2273
theorem derived2273 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2273 := by
  apply localUnsat_implies_entails f2273 [c279, c274, c2061] c2273 unsat2273 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c2061 := derived2061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2274 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨50, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2274 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2273, some c2268, some c155, some c164, some c2230, some c2008, some c12, some c172, some c184, some c1118, some c1972, some c2272, some c2050, some c2026, some c319, some c339, some c272, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2274 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2274 : lratChecker f2274 p2274 = .success := by decide +kernel
theorem unsat2274 : Unsatisfiable (PosFin 57) f2274 := by
  apply lratCheckerSound f2274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2274
  · intro a ha; simp [p2274] at ha; subst a; trivial
  · exact checked2274
theorem derived2274 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2274 := by
  apply localUnsat_implies_entails f2274 [c2273, c2268, c155, c164, c2230, c2008, c12, c172, c184, c1118, c1972, c2272, c2050, c2026, c319, c339, c272] c2274 unsat2274 (by rfl) a
  have h0 : Entails.eval a c2273 := derived2273 a h
  have h1 : Entails.eval a c2268 := derived2268 a h
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c2230 := derived2230 a h
  have h5 : Entails.eval a c2008 := derived2008 a h
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c1118 := derived1118 a h
  have h10 : Entails.eval a c1972 := derived1972 a h
  have h11 : Entails.eval a c2272 := derived2272 a h
  have h12 : Entails.eval a c2050 := derived2050 a h
  have h13 : Entails.eval a c2026 := derived2026 a h
  have h14 : Entails.eval a c319 := h 318 (by decide)
  have h15 : Entails.eval a c339 := h 338 (by decide)
  have h16 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2275 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2275 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2259, some c2253, some c101, some c379, some c968, some c2260, some c172, some c178, some c186, some c13, some c165, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2275 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2275 : lratChecker f2275 p2275 = .success := by decide +kernel
theorem unsat2275 : Unsatisfiable (PosFin 57) f2275 := by
  apply lratCheckerSound f2275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2275
  · intro a ha; simp [p2275] at ha; subst a; trivial
  · exact checked2275
theorem derived2275 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2275 := by
  apply localUnsat_implies_entails f2275 [c2259, c2253, c101, c379, c968, c2260, c172, c178, c186, c13, c165] c2275 unsat2275 (by rfl) a
  have h0 : Entails.eval a c2259 := derived2259 a h
  have h1 : Entails.eval a c2253 := derived2253 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c2260 := derived2260 a h
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2276 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2276 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c172, some c178, some c186, some c184, some c165, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p2276 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2276 : lratChecker f2276 p2276 = .success := by decide +kernel
theorem unsat2276 : Unsatisfiable (PosFin 57) f2276 := by
  apply lratCheckerSound f2276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2276
  · intro a ha; simp [p2276] at ha; subst a; trivial
  · exact checked2276
theorem derived2276 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2276 := by
  apply localUnsat_implies_entails f2276 [c172, c178, c186, c184, c165] c2276 unsat2276 (by rfl) a
  have h0 : Entails.eval a c172 := h 171 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2277 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2277 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2047, some c2061, some c277, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2277 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2277 : lratChecker f2277 p2277 = .success := by decide +kernel
theorem unsat2277 : Unsatisfiable (PosFin 57) f2277 := by
  apply lratCheckerSound f2277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2277
  · intro a ha; simp [p2277] at ha; subst a; trivial
  · exact checked2277
theorem derived2277 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2277 := by
  apply localUnsat_implies_entails f2277 [c2047, c2061, c277] c2277 unsat2277 (by rfl) a
  have h0 : Entails.eval a c2047 := derived2047 a h
  have h1 : Entails.eval a c2061 := derived2061 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2278 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨45, by decide⟩, false), (⟨12, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2278 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c277, some c1014, some c125, some c127, some c34, some c204, some c201, some c319, some c879, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2278 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2278 : lratChecker f2278 p2278 = .success := by decide +kernel
theorem unsat2278 : Unsatisfiable (PosFin 57) f2278 := by
  apply lratCheckerSound f2278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2278
  · intro a ha; simp [p2278] at ha; subst a; trivial
  · exact checked2278
theorem derived2278 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2278 := by
  apply localUnsat_implies_entails f2278 [c277, c1014, c125, c127, c34, c204, c201, c319, c879] c2278 unsat2278 (by rfl) a
  have h0 : Entails.eval a c277 := h 276 (by decide)
  have h1 : Entails.eval a c1014 := derived1014 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c879 := derived879 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2279 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2279 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2050, some c2026, some c317, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2279 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2279 : lratChecker f2279 p2279 = .success := by decide +kernel
theorem unsat2279 : Unsatisfiable (PosFin 57) f2279 := by
  apply lratCheckerSound f2279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2279
  · intro a ha; simp [p2279] at ha; subst a; trivial
  · exact checked2279
theorem derived2279 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2279 := by
  apply localUnsat_implies_entails f2279 [c2050, c2026, c317] c2279 unsat2279 (by rfl) a
  have h0 : Entails.eval a c2050 := derived2050 a h
  have h1 : Entails.eval a c2026 := derived2026 a h
  have h2 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2280 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2280 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2201, some c101, some c2271, some c2273, some c366, some c2253, some c2268, some c2259, some c2274, some c1051, some c374, some c2275, some c1118, some c67, some c1491, some c2276, some c2277, some c289, some c2279, some c314, some c329, some c270, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p2280 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2280 : lratChecker f2280 p2280 = .success := by decide +kernel
theorem unsat2280 : Unsatisfiable (PosFin 57) f2280 := by
  apply lratCheckerSound f2280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2280
  · intro a ha; simp [p2280] at ha; subst a; trivial
  · exact checked2280
theorem derived2280 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2280 := by
  apply localUnsat_implies_entails f2280 [c2201, c101, c2271, c2273, c366, c2253, c2268, c2259, c2274, c1051, c374, c2275, c1118, c67, c1491, c2276, c2277, c289, c2279, c314, c329, c270] c2280 unsat2280 (by rfl) a
  have h0 : Entails.eval a c2201 := derived2201 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c2271 := derived2271 a h
  have h3 : Entails.eval a c2273 := derived2273 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c2253 := derived2253 a h
  have h6 : Entails.eval a c2268 := derived2268 a h
  have h7 : Entails.eval a c2259 := derived2259 a h
  have h8 : Entails.eval a c2274 := derived2274 a h
  have h9 : Entails.eval a c1051 := derived1051 a h
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c2275 := derived2275 a h
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c1491 := derived1491 a h
  have h15 : Entails.eval a c2276 := derived2276 a h
  have h16 : Entails.eval a c2277 := derived2277 a h
  have h17 : Entails.eval a c289 := h 288 (by decide)
  have h18 : Entails.eval a c2279 := derived2279 a h
  have h19 : Entails.eval a c314 := h 313 (by decide)
  have h20 : Entails.eval a c329 := h 328 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2280

end CochromaticTwenty.Certificates.B16_8_2
