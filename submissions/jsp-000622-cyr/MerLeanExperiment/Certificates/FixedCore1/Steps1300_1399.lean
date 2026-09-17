import MerLeanExperiment.Certificates.FixedCore1.Steps1200_1299

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7181 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c938, some c953, some c2186, some c2640, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7181 : lratChecker f7181 p7181 = .success := by decide +kernel
theorem unsat7181 : Unsatisfiable (PosFin 65) f7181 := by
  apply lratCheckerSound f7181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7181
  · intro a ha; simp [p7181] at ha; subst a; trivial
  · exact checked7181
theorem derived7181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7181 := by
  apply localUnsat_implies_entails f7181 [c938, c953, c2186, c2640] c7181 unsat7181 (by rfl) a
  have h0 : Entails.eval a c938 := h 937 (by decide)
  have h1 : Entails.eval a c953 := h 952 (by decide)
  have h2 : Entails.eval a c2186 := h 2185 (by decide)
  have h3 : Entails.eval a c2640 := h 2639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7182 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7140, some c7139, some c191, some c7159, some c294, some c297, some c193, some c178, some c7181, some c2182, some c2214, some c937, some c2637, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7182 : lratChecker f7182 p7182 = .success := by decide +kernel
theorem unsat7182 : Unsatisfiable (PosFin 65) f7182 := by
  apply lratCheckerSound f7182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7182
  · intro a ha; simp [p7182] at ha; subst a; trivial
  · exact checked7182
theorem derived7182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7182 := by
  apply localUnsat_implies_entails f7182 [c7174, c7140, c7139, c191, c7159, c294, c297, c193, c178, c7181, c2182, c2214, c937, c2637] c7182 unsat7182 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c7159 := derived7159 a h
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c7181 := derived7181 a h
  have h10 : Entails.eval a c2182 := h 2181 (by decide)
  have h11 : Entails.eval a c2214 := h 2213 (by decide)
  have h12 : Entails.eval a c937 := h 936 (by decide)
  have h13 : Entails.eval a c2637 := h 2636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7183 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c347, some c1043, some c2088, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7183 : lratChecker f7183 p7183 = .success := by decide +kernel
theorem unsat7183 : Unsatisfiable (PosFin 65) f7183 := by
  apply lratCheckerSound f7183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7183
  · intro a ha; simp [p7183] at ha; subst a; trivial
  · exact checked7183
theorem derived7183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7183 := by
  apply localUnsat_implies_entails f7183 [c347, c1043, c2088] c7183 unsat7183 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c1043 := h 1042 (by decide)
  have h2 : Entails.eval a c2088 := h 2087 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7184 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7140, some c7139, some c7180, some c7182, some c7138, some c180, some c193, some c189, some c299, some c297, some c186, some c188, some c295, some c202, some c7183, some c2204, some c2220, some c2095, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7184 : lratChecker f7184 p7184 = .success := by decide +kernel
theorem unsat7184 : Unsatisfiable (PosFin 65) f7184 := by
  apply lratCheckerSound f7184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7184
  · intro a ha; simp [p7184] at ha; subst a; trivial
  · exact checked7184
theorem derived7184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7184 := by
  apply localUnsat_implies_entails f7184 [c7174, c7140, c7139, c7180, c7182, c7138, c180, c193, c189, c299, c297, c186, c188, c295, c202, c7183, c2204, c2220, c2095] c7184 unsat7184 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c7180 := derived7180 a h
  have h4 : Entails.eval a c7182 := derived7182 a h
  have h5 : Entails.eval a c7138 := derived7138 a h
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c295 := h 294 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c7183 := derived7183 a h
  have h16 : Entails.eval a c2204 := h 2203 (by decide)
  have h17 : Entails.eval a c2220 := h 2219 (by decide)
  have h18 : Entails.eval a c2095 := h 2094 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7185 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7139, some c6688, some c6691, some c746, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7185 : lratChecker f7185 p7185 = .success := by decide +kernel
theorem unsat7185 : Unsatisfiable (PosFin 65) f7185 := by
  apply lratCheckerSound f7185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7185
  · intro a ha; simp [p7185] at ha; subst a; trivial
  · exact checked7185
theorem derived7185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7185 := by
  apply localUnsat_implies_entails f7185 [c7174, c7139, c6688, c6691, c746] c7185 unsat7185 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c6688 := derived6688 a h
  have h3 : Entails.eval a c6691 := derived6691 a h
  have h4 : Entails.eval a c746 := h 745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7186 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7140, some c7139, some c191, some c297, some c193, some c178, some c294, some c7175, some c7184, some c953, some c1243, some c7170, some c2081, some c2130, some c7185, some c210, some c211, some c245, some c214, some c326, some c369, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7186 : lratChecker f7186 p7186 = .success := by decide +kernel
theorem unsat7186 : Unsatisfiable (PosFin 65) f7186 := by
  apply lratCheckerSound f7186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7186
  · intro a ha; simp [p7186] at ha; subst a; trivial
  · exact checked7186
theorem derived7186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7186 := by
  apply localUnsat_implies_entails f7186 [c7174, c7140, c7139, c191, c297, c193, c178, c294, c7175, c7184, c953, c1243, c7170, c2081, c2130, c7185, c210, c211, c245, c214, c326, c369] c7186 unsat7186 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  have h8 : Entails.eval a c7175 := derived7175 a h
  have h9 : Entails.eval a c7184 := derived7184 a h
  have h10 : Entails.eval a c953 := h 952 (by decide)
  have h11 : Entails.eval a c1243 := h 1242 (by decide)
  have h12 : Entails.eval a c7170 := derived7170 a h
  have h13 : Entails.eval a c2081 := h 2080 (by decide)
  have h14 : Entails.eval a c2130 := h 2129 (by decide)
  have h15 : Entails.eval a c7185 := derived7185 a h
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c211 := h 210 (by decide)
  have h18 : Entails.eval a c245 := h 244 (by decide)
  have h19 : Entails.eval a c214 := h 213 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7187 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7175, some c7184, some c7174, some c7140, some c7139, some c191, some c7159, some c297, some c193, some c184, some c7186, some c937, some c952, some c1247, some c1259, some c2348, some c2636, some c2128, some c2270, some c728, some c7185, some c186, some c210, some c211, some c245, some c326, some c112, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked7187 : lratChecker f7187 p7187 = .success := by decide +kernel
theorem unsat7187 : Unsatisfiable (PosFin 65) f7187 := by
  apply lratCheckerSound f7187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7187
  · intro a ha; simp [p7187] at ha; subst a; trivial
  · exact checked7187
theorem derived7187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7187 := by
  apply localUnsat_implies_entails f7187 [c7175, c7184, c7174, c7140, c7139, c191, c7159, c297, c193, c184, c7186, c937, c952, c1247, c1259, c2348, c2636, c2128, c2270, c728, c7185, c186, c210, c211, c245, c326, c112] c7187 unsat7187 (by rfl) a
  have h0 : Entails.eval a c7175 := derived7175 a h
  have h1 : Entails.eval a c7184 := derived7184 a h
  have h2 : Entails.eval a c7174 := derived7174 a h
  have h3 : Entails.eval a c7140 := derived7140 a h
  have h4 : Entails.eval a c7139 := derived7139 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c7159 := derived7159 a h
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c7186 := derived7186 a h
  have h11 : Entails.eval a c937 := h 936 (by decide)
  have h12 : Entails.eval a c952 := h 951 (by decide)
  have h13 : Entails.eval a c1247 := h 1246 (by decide)
  have h14 : Entails.eval a c1259 := h 1258 (by decide)
  have h15 : Entails.eval a c2348 := h 2347 (by decide)
  have h16 : Entails.eval a c2636 := h 2635 (by decide)
  have h17 : Entails.eval a c2128 := h 2127 (by decide)
  have h18 : Entails.eval a c2270 := h 2269 (by decide)
  have h19 : Entails.eval a c728 := h 727 (by decide)
  have h20 : Entails.eval a c7185 := derived7185 a h
  have h21 : Entails.eval a c186 := h 185 (by decide)
  have h22 : Entails.eval a c210 := h 209 (by decide)
  have h23 : Entails.eval a c211 := h 210 (by decide)
  have h24 : Entails.eval a c245 := h 244 (by decide)
  have h25 : Entails.eval a c326 := h 325 (by decide)
  have h26 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7188 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7140, some c6688, some c6691, some c6673, some c77, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7188 : lratChecker f7188 p7188 = .success := by decide +kernel
theorem unsat7188 : Unsatisfiable (PosFin 65) f7188 := by
  apply lratCheckerSound f7188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7188
  · intro a ha; simp [p7188] at ha; subst a; trivial
  · exact checked7188
theorem derived7188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7188 := by
  apply localUnsat_implies_entails f7188 [c7174, c7140, c6688, c6691, c6673, c77] c7188 unsat7188 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c6688 := derived6688 a h
  have h3 : Entails.eval a c6691 := derived6691 a h
  have h4 : Entails.eval a c6673 := derived6673 a h
  have h5 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7189 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7187, some c7174, some c7138, some c193, some c189, some c7139, some c299, some c188, some c7175, some c7140, some c248, some c347, some c397, some c2471, some c2625, some c2088, some c7188, some c210, some c211, some c964, some c6689, some c326, some c1253, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked7189 : lratChecker f7189 p7189 = .success := by decide +kernel
theorem unsat7189 : Unsatisfiable (PosFin 65) f7189 := by
  apply lratCheckerSound f7189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7189
  · intro a ha; simp [p7189] at ha; subst a; trivial
  · exact checked7189
theorem derived7189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7189 := by
  apply localUnsat_implies_entails f7189 [c7187, c7174, c7138, c193, c189, c7139, c299, c188, c7175, c7140, c248, c347, c397, c2471, c2625, c2088, c7188, c210, c211, c964, c6689, c326, c1253] c7189 unsat7189 (by rfl) a
  have h0 : Entails.eval a c7187 := derived7187 a h
  have h1 : Entails.eval a c7174 := derived7174 a h
  have h2 : Entails.eval a c7138 := derived7138 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c7139 := derived7139 a h
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c7175 := derived7175 a h
  have h9 : Entails.eval a c7140 := derived7140 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c347 := h 346 (by decide)
  have h12 : Entails.eval a c397 := h 396 (by decide)
  have h13 : Entails.eval a c2471 := h 2470 (by decide)
  have h14 : Entails.eval a c2625 := h 2624 (by decide)
  have h15 : Entails.eval a c2088 := h 2087 (by decide)
  have h16 : Entails.eval a c7188 := derived7188 a h
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c211 := h 210 (by decide)
  have h19 : Entails.eval a c964 := h 963 (by decide)
  have h20 : Entails.eval a c6689 := derived6689 a h
  have h21 : Entails.eval a c326 := h 325 (by decide)
  have h22 : Entails.eval a c1253 := h 1252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7190 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨20, by decide⟩, true), (⟨30, by decide⟩, false), (⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c193, some c6688, some c6691, some c6762, some c77, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7190 : lratChecker f7190 p7190 = .success := by decide +kernel
theorem unsat7190 : Unsatisfiable (PosFin 65) f7190 := by
  apply lratCheckerSound f7190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7190
  · intro a ha; simp [p7190] at ha; subst a; trivial
  · exact checked7190
theorem derived7190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7190 := by
  apply localUnsat_implies_entails f7190 [c7174, c193, c6688, c6691, c6762, c77] c7190 unsat7190 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c6688 := derived6688 a h
  have h3 : Entails.eval a c6691 := derived6691 a h
  have h4 : Entails.eval a c6762 := derived6762 a h
  have h5 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7191 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7187, some c7138, some c193, some c189, some c7139, some c299, some c188, some c202, some c7140, some c180, some c186, some c295, some c297, some c7175, some c7189, some c343, some c263, some c390, some c2095, some c2475, some c2631, some c7190, some c210, some c211, some c964, some c6689, some c326, some c1253, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked7191 : lratChecker f7191 p7191 = .success := by decide +kernel
theorem unsat7191 : Unsatisfiable (PosFin 65) f7191 := by
  apply lratCheckerSound f7191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7191
  · intro a ha; simp [p7191] at ha; subst a; trivial
  · exact checked7191
theorem derived7191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7191 := by
  apply localUnsat_implies_entails f7191 [c7174, c7187, c7138, c193, c189, c7139, c299, c188, c202, c7140, c180, c186, c295, c297, c7175, c7189, c343, c263, c390, c2095, c2475, c2631, c7190, c210, c211, c964, c6689, c326, c1253] c7191 unsat7191 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7187 := derived7187 a h
  have h2 : Entails.eval a c7138 := derived7138 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c7139 := derived7139 a h
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c7140 := derived7140 a h
  have h10 : Entails.eval a c180 := h 179 (by decide)
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c7175 := derived7175 a h
  have h15 : Entails.eval a c7189 := derived7189 a h
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c263 := h 262 (by decide)
  have h18 : Entails.eval a c390 := h 389 (by decide)
  have h19 : Entails.eval a c2095 := h 2094 (by decide)
  have h20 : Entails.eval a c2475 := h 2474 (by decide)
  have h21 : Entails.eval a c2631 := h 2630 (by decide)
  have h22 : Entails.eval a c7190 := derived7190 a h
  have h23 : Entails.eval a c210 := h 209 (by decide)
  have h24 : Entails.eval a c211 := h 210 (by decide)
  have h25 : Entails.eval a c964 := h 963 (by decide)
  have h26 : Entails.eval a c6689 := derived6689 a h
  have h27 : Entails.eval a c326 := h 325 (by decide)
  have h28 : Entails.eval a c1253 := h 1252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7192 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7139, some c7140, some c7175, some c7187, some c7138, some c180, some c193, some c189, some c299, some c186, some c188, some c295, some c202, some c7191, some c7183, some c343, some c1046, some c2095, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7192 : lratChecker f7192 p7192 = .success := by decide +kernel
theorem unsat7192 : Unsatisfiable (PosFin 65) f7192 := by
  apply lratCheckerSound f7192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7192
  · intro a ha; simp [p7192] at ha; subst a; trivial
  · exact checked7192
theorem derived7192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7192 := by
  apply localUnsat_implies_entails f7192 [c7174, c7139, c7140, c7175, c7187, c7138, c180, c193, c189, c299, c186, c188, c295, c202, c7191, c7183, c343, c1046, c2095] c7192 unsat7192 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c7140 := derived7140 a h
  have h3 : Entails.eval a c7175 := derived7175 a h
  have h4 : Entails.eval a c7187 := derived7187 a h
  have h5 : Entails.eval a c7138 := derived7138 a h
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c186 := h 185 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c7191 := derived7191 a h
  have h15 : Entails.eval a c7183 := derived7183 a h
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c1046 := h 1045 (by decide)
  have h18 : Entails.eval a c2095 := h 2094 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7193 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1612, some c1670, some c1679, some c2538, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7193 : lratChecker f7193 p7193 = .success := by decide +kernel
theorem unsat7193 : Unsatisfiable (PosFin 65) f7193 := by
  apply lratCheckerSound f7193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7193
  · intro a ha; simp [p7193] at ha; subst a; trivial
  · exact checked7193
theorem derived7193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7193 := by
  apply localUnsat_implies_entails f7193 [c1612, c1670, c1679, c2538] c7193 unsat7193 (by rfl) a
  have h0 : Entails.eval a c1612 := h 1611 (by decide)
  have h1 : Entails.eval a c1670 := h 1669 (by decide)
  have h2 : Entails.eval a c1679 := h 1678 (by decide)
  have h3 : Entails.eval a c2538 := h 2537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7194 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7193, some c1631, some c1669, some c1611, some c1094, some c1380, some c273, some c2348, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7194 : lratChecker f7194 p7194 = .success := by decide +kernel
theorem unsat7194 : Unsatisfiable (PosFin 65) f7194 := by
  apply lratCheckerSound f7194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7194
  · intro a ha; simp [p7194] at ha; subst a; trivial
  · exact checked7194
theorem derived7194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7194 := by
  apply localUnsat_implies_entails f7194 [c7193, c1631, c1669, c1611, c1094, c1380, c273, c2348] c7194 unsat7194 (by rfl) a
  have h0 : Entails.eval a c7193 := derived7193 a h
  have h1 : Entails.eval a c1631 := h 1630 (by decide)
  have h2 : Entails.eval a c1669 := h 1668 (by decide)
  have h3 : Entails.eval a c1611 := h 1610 (by decide)
  have h4 : Entails.eval a c1094 := h 1093 (by decide)
  have h5 : Entails.eval a c1380 := h 1379 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7195 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1625, some c275, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7195 : lratChecker f7195 p7195 = .success := by decide +kernel
theorem unsat7195 : Unsatisfiable (PosFin 65) f7195 := by
  apply lratCheckerSound f7195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7195
  · intro a ha; simp [p7195] at ha; subst a; trivial
  · exact checked7195
theorem derived7195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7195 := by
  apply localUnsat_implies_entails f7195 [c1625, c275] c7195 unsat7195 (by rfl) a
  have h0 : Entails.eval a c1625 := h 1624 (by decide)
  have h1 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7196 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7193, some c1669, some c1611, some c7194, some c2227, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7196 : lratChecker f7196 p7196 = .success := by decide +kernel
theorem unsat7196 : Unsatisfiable (PosFin 65) f7196 := by
  apply lratCheckerSound f7196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7196
  · intro a ha; simp [p7196] at ha; subst a; trivial
  · exact checked7196
theorem derived7196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7196 := by
  apply localUnsat_implies_entails f7196 [c7193, c1669, c1611, c7194, c2227] c7196 unsat7196 (by rfl) a
  have h0 : Entails.eval a c7193 := derived7193 a h
  have h1 : Entails.eval a c1669 := h 1668 (by decide)
  have h2 : Entails.eval a c1611 := h 1610 (by decide)
  have h3 : Entails.eval a c7194 := derived7194 a h
  have h4 : Entails.eval a c2227 := h 2226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7197 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c251, some c1712, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7197 : lratChecker f7197 p7197 = .success := by decide +kernel
theorem unsat7197 : Unsatisfiable (PosFin 65) f7197 := by
  apply lratCheckerSound f7197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7197
  · intro a ha; simp [p7197] at ha; subst a; trivial
  · exact checked7197
theorem derived7197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7197 := by
  apply localUnsat_implies_entails f7197 [c251, c1712] c7197 unsat7197 (by rfl) a
  have h0 : Entails.eval a c251 := h 250 (by decide)
  have h1 : Entails.eval a c1712 := h 1711 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7198 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7193, some c7195, some c7197, some c1611, some c1567, some c7196, some c273, some c253, some c767, some c335, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7198 : lratChecker f7198 p7198 = .success := by decide +kernel
theorem unsat7198 : Unsatisfiable (PosFin 65) f7198 := by
  apply lratCheckerSound f7198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7198
  · intro a ha; simp [p7198] at ha; subst a; trivial
  · exact checked7198
theorem derived7198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7198 := by
  apply localUnsat_implies_entails f7198 [c7193, c7195, c7197, c1611, c1567, c7196, c273, c253, c767, c335] c7198 unsat7198 (by rfl) a
  have h0 : Entails.eval a c7193 := derived7193 a h
  have h1 : Entails.eval a c7195 := derived7195 a h
  have h2 : Entails.eval a c7197 := derived7197 a h
  have h3 : Entails.eval a c1611 := h 1610 (by decide)
  have h4 : Entails.eval a c1567 := h 1566 (by decide)
  have h5 : Entails.eval a c7196 := derived7196 a h
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c253 := h 252 (by decide)
  have h8 : Entails.eval a c767 := h 766 (by decide)
  have h9 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7199 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1566, some c1597, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7199 : lratChecker f7199 p7199 = .success := by decide +kernel
theorem unsat7199 : Unsatisfiable (PosFin 65) f7199 := by
  apply lratCheckerSound f7199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7199
  · intro a ha; simp [p7199] at ha; subst a; trivial
  · exact checked7199
theorem derived7199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7199 := by
  apply localUnsat_implies_entails f7199 [c1566, c1597] c7199 unsat7199 (by rfl) a
  have h0 : Entails.eval a c1566 := h 1565 (by decide)
  have h1 : Entails.eval a c1597 := h 1596 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7200 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7193, some c7198, some c7199, some c358, some c337, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7200 : lratChecker f7200 p7200 = .success := by decide +kernel
theorem unsat7200 : Unsatisfiable (PosFin 65) f7200 := by
  apply lratCheckerSound f7200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7200
  · intro a ha; simp [p7200] at ha; subst a; trivial
  · exact checked7200
theorem derived7200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7200 := by
  apply localUnsat_implies_entails f7200 [c7193, c7198, c7199, c358, c337] c7200 unsat7200 (by rfl) a
  have h0 : Entails.eval a c7193 := derived7193 a h
  have h1 : Entails.eval a c7198 := derived7198 a h
  have h2 : Entails.eval a c7199 := derived7199 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7201 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1631, some c1639, some c1634, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7201 : lratChecker f7201 p7201 = .success := by decide +kernel
theorem unsat7201 : Unsatisfiable (PosFin 65) f7201 := by
  apply lratCheckerSound f7201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7201
  · intro a ha; simp [p7201] at ha; subst a; trivial
  · exact checked7201
theorem derived7201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7201 := by
  apply localUnsat_implies_entails f7201 [c1631, c1639, c1634] c7201 unsat7201 (by rfl) a
  have h0 : Entails.eval a c1631 := h 1630 (by decide)
  have h1 : Entails.eval a c1639 := h 1638 (by decide)
  have h2 : Entails.eval a c1634 := h 1633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7202 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1569, some c2186, some c2198, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7202 : lratChecker f7202 p7202 = .success := by decide +kernel
theorem unsat7202 : Unsatisfiable (PosFin 65) f7202 := by
  apply lratCheckerSound f7202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7202
  · intro a ha; simp [p7202] at ha; subst a; trivial
  · exact checked7202
theorem derived7202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7202 := by
  apply localUnsat_implies_entails f7202 [c1569, c2186, c2198] c7202 unsat7202 (by rfl) a
  have h0 : Entails.eval a c1569 := h 1568 (by decide)
  have h1 : Entails.eval a c2186 := h 2185 (by decide)
  have h2 : Entails.eval a c2198 := h 2197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7203 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c251, some c1618, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7203 : lratChecker f7203 p7203 = .success := by decide +kernel
theorem unsat7203 : Unsatisfiable (PosFin 65) f7203 := by
  apply lratCheckerSound f7203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7203
  · intro a ha; simp [p7203] at ha; subst a; trivial
  · exact checked7203
theorem derived7203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7203 := by
  apply localUnsat_implies_entails f7203 [c251, c1618] c7203 unsat7203 (by rfl) a
  have h0 : Entails.eval a c251 := h 250 (by decide)
  have h1 : Entails.eval a c1618 := h 1617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7204 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1034, some c1032, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7204 : lratChecker f7204 p7204 = .success := by decide +kernel
theorem unsat7204 : Unsatisfiable (PosFin 65) f7204 := by
  apply lratCheckerSound f7204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7204
  · intro a ha; simp [p7204] at ha; subst a; trivial
  · exact checked7204
theorem derived7204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7204 := by
  apply localUnsat_implies_entails f7204 [c1034, c1032] c7204 unsat7204 (by rfl) a
  have h0 : Entails.eval a c1034 := h 1033 (by decide)
  have h1 : Entails.eval a c1032 := h 1031 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7205 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7195, some c7203, some c7204, some c7201, some c7202, some c2184, some c7199, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7205 : lratChecker f7205 p7205 = .success := by decide +kernel
theorem unsat7205 : Unsatisfiable (PosFin 65) f7205 := by
  apply lratCheckerSound f7205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7205
  · intro a ha; simp [p7205] at ha; subst a; trivial
  · exact checked7205
theorem derived7205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7205 := by
  apply localUnsat_implies_entails f7205 [c7195, c7203, c7204, c7201, c7202, c2184, c7199] c7205 unsat7205 (by rfl) a
  have h0 : Entails.eval a c7195 := derived7195 a h
  have h1 : Entails.eval a c7203 := derived7203 a h
  have h2 : Entails.eval a c7204 := derived7204 a h
  have h3 : Entails.eval a c7201 := derived7201 a h
  have h4 : Entails.eval a c7202 := derived7202 a h
  have h5 : Entails.eval a c2184 := h 2183 (by decide)
  have h6 : Entails.eval a c7199 := derived7199 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7206 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1583, some c1597, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7206 : lratChecker f7206 p7206 = .success := by decide +kernel
theorem unsat7206 : Unsatisfiable (PosFin 65) f7206 := by
  apply lratCheckerSound f7206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7206
  · intro a ha; simp [p7206] at ha; subst a; trivial
  · exact checked7206
theorem derived7206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7206 := by
  apply localUnsat_implies_entails f7206 [c1583, c1597] c7206 unsat7206 (by rfl) a
  have h0 : Entails.eval a c1583 := h 1582 (by decide)
  have h1 : Entails.eval a c1597 := h 1596 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7207 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7200, some c7205, some c7206, some c358, some c337, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7207 : lratChecker f7207 p7207 = .success := by decide +kernel
theorem unsat7207 : Unsatisfiable (PosFin 65) f7207 := by
  apply lratCheckerSound f7207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7207
  · intro a ha; simp [p7207] at ha; subst a; trivial
  · exact checked7207
theorem derived7207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7207 := by
  apply localUnsat_implies_entails f7207 [c7200, c7205, c7206, c358, c337] c7207 unsat7207 (by rfl) a
  have h0 : Entails.eval a c7200 := derived7200 a h
  have h1 : Entails.eval a c7205 := derived7205 a h
  have h2 : Entails.eval a c7206 := derived7206 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7208 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7207, some c334, some c1580, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7208 : lratChecker f7208 p7208 = .success := by decide +kernel
theorem unsat7208 : Unsatisfiable (PosFin 65) f7208 := by
  apply lratCheckerSound f7208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7208
  · intro a ha; simp [p7208] at ha; subst a; trivial
  · exact checked7208
theorem derived7208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7208 := by
  apply localUnsat_implies_entails f7208 [c7207, c334, c1580] c7208 unsat7208 (by rfl) a
  have h0 : Entails.eval a c7207 := derived7207 a h
  have h1 : Entails.eval a c334 := h 333 (by decide)
  have h2 : Entails.eval a c1580 := h 1579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7209 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7195, some c7197, some c256, some c1716, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7209 : lratChecker f7209 p7209 = .success := by decide +kernel
theorem unsat7209 : Unsatisfiable (PosFin 65) f7209 := by
  apply lratCheckerSound f7209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7209
  · intro a ha; simp [p7209] at ha; subst a; trivial
  · exact checked7209
theorem derived7209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7209 := by
  apply localUnsat_implies_entails f7209 [c7195, c7197, c256, c1716] c7209 unsat7209 (by rfl) a
  have h0 : Entails.eval a c7195 := derived7195 a h
  have h1 : Entails.eval a c7197 := derived7197 a h
  have h2 : Entails.eval a c256 := h 255 (by decide)
  have h3 : Entails.eval a c1716 := h 1715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7210 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c256, some c1716, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7210 : lratChecker f7210 p7210 = .success := by decide +kernel
theorem unsat7210 : Unsatisfiable (PosFin 65) f7210 := by
  apply lratCheckerSound f7210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7210
  · intro a ha; simp [p7210] at ha; subst a; trivial
  · exact checked7210
theorem derived7210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7210 := by
  apply localUnsat_implies_entails f7210 [c256, c1716] c7210 unsat7210 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c1716 := h 1715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7211 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6662, some c6722, some c6744, some c77, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7211 : lratChecker f7211 p7211 = .success := by decide +kernel
theorem unsat7211 : Unsatisfiable (PosFin 65) f7211 := by
  apply lratCheckerSound f7211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7211
  · intro a ha; simp [p7211] at ha; subst a; trivial
  · exact checked7211
theorem derived7211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7211 := by
  apply localUnsat_implies_entails f7211 [c6662, c6722, c6744, c77] c7211 unsat7211 (by rfl) a
  have h0 : Entails.eval a c6662 := derived6662 a h
  have h1 : Entails.eval a c6722 := derived6722 a h
  have h2 : Entails.eval a c6744 := derived6744 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7212 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c218, some c248, some c347, some c397, some c1768, some c1774, some c2471, some c2597, some c1585, some c2088, some c1803, some c1695, some c2457, some c1691, some c1601, some c1570, some c7211, some c6, some c7, some c3135, some c84, some c5, some c36, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked7212 : lratChecker f7212 p7212 = .success := by decide +kernel
theorem unsat7212 : Unsatisfiable (PosFin 65) f7212 := by
  apply lratCheckerSound f7212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7212
  · intro a ha; simp [p7212] at ha; subst a; trivial
  · exact checked7212
theorem derived7212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7212 := by
  apply localUnsat_implies_entails f7212 [c7192, c218, c248, c347, c397, c1768, c1774, c2471, c2597, c1585, c2088, c1803, c1695, c2457, c1691, c1601, c1570, c7211, c6, c7, c3135, c84, c5, c36] c7212 unsat7212 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c218 := h 217 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c397 := h 396 (by decide)
  have h5 : Entails.eval a c1768 := h 1767 (by decide)
  have h6 : Entails.eval a c1774 := h 1773 (by decide)
  have h7 : Entails.eval a c2471 := h 2470 (by decide)
  have h8 : Entails.eval a c2597 := h 2596 (by decide)
  have h9 : Entails.eval a c1585 := h 1584 (by decide)
  have h10 : Entails.eval a c2088 := h 2087 (by decide)
  have h11 : Entails.eval a c1803 := h 1802 (by decide)
  have h12 : Entails.eval a c1695 := h 1694 (by decide)
  have h13 : Entails.eval a c2457 := h 2456 (by decide)
  have h14 : Entails.eval a c1691 := h 1690 (by decide)
  have h15 : Entails.eval a c1601 := h 1600 (by decide)
  have h16 : Entails.eval a c1570 := h 1569 (by decide)
  have h17 : Entails.eval a c7211 := derived7211 a h
  have h18 : Entails.eval a c6 := h 5 (by decide)
  have h19 : Entails.eval a c7 := h 6 (by decide)
  have h20 : Entails.eval a c3135 := h 3134 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c5 := h 4 (by decide)
  have h23 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7213 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6662, some c6761, some c6762, some c77, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7213 : lratChecker f7213 p7213 = .success := by decide +kernel
theorem unsat7213 : Unsatisfiable (PosFin 65) f7213 := by
  apply lratCheckerSound f7213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7213
  · intro a ha; simp [p7213] at ha; subst a; trivial
  · exact checked7213
theorem derived7213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7213 := by
  apply localUnsat_implies_entails f7213 [c6662, c6761, c6762, c77] c7213 unsat7213 (by rfl) a
  have h0 : Entails.eval a c6662 := derived6662 a h
  have h1 : Entails.eval a c6761 := derived6761 a h
  have h2 : Entails.eval a c6762 := derived6762 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7214 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c7208, some c7209, some c7210, some c7212, some c226, some c343, some c260, some c1768, some c1774, some c1583, some c1585, some c2475, some c1717, some c390, some c1692, some c1601, some c1695, some c2631, some c1570, some c7213, some c6, some c7, some c3192, some c3225, some c101, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked7214 : lratChecker f7214 p7214 = .success := by decide +kernel
theorem unsat7214 : Unsatisfiable (PosFin 65) f7214 := by
  apply lratCheckerSound f7214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7214
  · intro a ha; simp [p7214] at ha; subst a; trivial
  · exact checked7214
theorem derived7214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7214 := by
  apply localUnsat_implies_entails f7214 [c7192, c7208, c7209, c7210, c7212, c226, c343, c260, c1768, c1774, c1583, c1585, c2475, c1717, c390, c1692, c1601, c1695, c2631, c1570, c7213, c6, c7, c3192, c3225, c101] c7214 unsat7214 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c7208 := derived7208 a h
  have h2 : Entails.eval a c7209 := derived7209 a h
  have h3 : Entails.eval a c7210 := derived7210 a h
  have h4 : Entails.eval a c7212 := derived7212 a h
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c1768 := h 1767 (by decide)
  have h9 : Entails.eval a c1774 := h 1773 (by decide)
  have h10 : Entails.eval a c1583 := h 1582 (by decide)
  have h11 : Entails.eval a c1585 := h 1584 (by decide)
  have h12 : Entails.eval a c2475 := h 2474 (by decide)
  have h13 : Entails.eval a c1717 := h 1716 (by decide)
  have h14 : Entails.eval a c390 := h 389 (by decide)
  have h15 : Entails.eval a c1692 := h 1691 (by decide)
  have h16 : Entails.eval a c1601 := h 1600 (by decide)
  have h17 : Entails.eval a c1695 := h 1694 (by decide)
  have h18 : Entails.eval a c2631 := h 2630 (by decide)
  have h19 : Entails.eval a c1570 := h 1569 (by decide)
  have h20 : Entails.eval a c7213 := derived7213 a h
  have h21 : Entails.eval a c6 := h 5 (by decide)
  have h22 : Entails.eval a c7 := h 6 (by decide)
  have h23 : Entails.eval a c3192 := h 3191 (by decide)
  have h24 : Entails.eval a c3225 := h 3224 (by decide)
  have h25 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7215 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1583, some c1585, some c1591, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7215 : lratChecker f7215 p7215 = .success := by decide +kernel
theorem unsat7215 : Unsatisfiable (PosFin 65) f7215 := by
  apply lratCheckerSound f7215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7215
  · intro a ha; simp [p7215] at ha; subst a; trivial
  · exact checked7215
theorem derived7215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7215 := by
  apply localUnsat_implies_entails f7215 [c1583, c1585, c1591] c7215 unsat7215 (by rfl) a
  have h0 : Entails.eval a c1583 := h 1582 (by decide)
  have h1 : Entails.eval a c1585 := h 1584 (by decide)
  have h2 : Entails.eval a c1591 := h 1590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7216 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c7208, some c7209, some c7214, some c7215, some c330, some c337, some c342, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7216 : lratChecker f7216 p7216 = .success := by decide +kernel
theorem unsat7216 : Unsatisfiable (PosFin 65) f7216 := by
  apply lratCheckerSound f7216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7216
  · intro a ha; simp [p7216] at ha; subst a; trivial
  · exact checked7216
theorem derived7216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7216 := by
  apply localUnsat_implies_entails f7216 [c7192, c7208, c7209, c7214, c7215, c330, c337, c342] c7216 unsat7216 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c7208 := derived7208 a h
  have h2 : Entails.eval a c7209 := derived7209 a h
  have h3 : Entails.eval a c7214 := derived7214 a h
  have h4 : Entails.eval a c7215 := derived7215 a h
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c337 := h 336 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7217 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7195, some c7203, some c256, some c1621, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7217 : lratChecker f7217 p7217 = .success := by decide +kernel
theorem unsat7217 : Unsatisfiable (PosFin 65) f7217 := by
  apply lratCheckerSound f7217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7217
  · intro a ha; simp [p7217] at ha; subst a; trivial
  · exact checked7217
theorem derived7217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7217 := by
  apply localUnsat_implies_entails f7217 [c7195, c7203, c256, c1621] c7217 unsat7217 (by rfl) a
  have h0 : Entails.eval a c7195 := derived7195 a h
  have h1 : Entails.eval a c7203 := derived7203 a h
  have h2 : Entails.eval a c256 := h 255 (by decide)
  have h3 : Entails.eval a c1621 := h 1620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7218 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c337, some c342, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7218 : lratChecker f7218 p7218 = .success := by decide +kernel
theorem unsat7218 : Unsatisfiable (PosFin 65) f7218 := by
  apply lratCheckerSound f7218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7218
  · intro a ha; simp [p7218] at ha; subst a; trivial
  · exact checked7218
theorem derived7218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7218 := by
  apply localUnsat_implies_entails f7218 [c337, c342] c7218 unsat7218 (by rfl) a
  have h0 : Entails.eval a c337 := h 336 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7219 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7208, some c7217, some c7183, some c7218, some c1593, some c2094, some c1045, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7219 : lratChecker f7219 p7219 = .success := by decide +kernel
theorem unsat7219 : Unsatisfiable (PosFin 65) f7219 := by
  apply lratCheckerSound f7219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7219
  · intro a ha; simp [p7219] at ha; subst a; trivial
  · exact checked7219
theorem derived7219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7219 := by
  apply localUnsat_implies_entails f7219 [c7208, c7217, c7183, c7218, c1593, c2094, c1045] c7219 unsat7219 (by rfl) a
  have h0 : Entails.eval a c7208 := derived7208 a h
  have h1 : Entails.eval a c7217 := derived7217 a h
  have h2 : Entails.eval a c7183 := derived7183 a h
  have h3 : Entails.eval a c7218 := derived7218 a h
  have h4 : Entails.eval a c1593 := h 1592 (by decide)
  have h5 : Entails.eval a c2094 := h 2093 (by decide)
  have h6 : Entails.eval a c1045 := h 1044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7220 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c7208, some c7217, some c7216, some c7219, some c7215, some c330, some c337, some c342, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7220 : lratChecker f7220 p7220 = .success := by decide +kernel
theorem unsat7220 : Unsatisfiable (PosFin 65) f7220 := by
  apply lratCheckerSound f7220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7220
  · intro a ha; simp [p7220] at ha; subst a; trivial
  · exact checked7220
theorem derived7220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7220 := by
  apply localUnsat_implies_entails f7220 [c7192, c7208, c7217, c7216, c7219, c7215, c330, c337, c342] c7220 unsat7220 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c7208 := derived7208 a h
  have h2 : Entails.eval a c7217 := derived7217 a h
  have h3 : Entails.eval a c7216 := derived7216 a h
  have h4 : Entails.eval a c7219 := derived7219 a h
  have h5 : Entails.eval a c7215 := derived7215 a h
  have h6 : Entails.eval a c330 := h 329 (by decide)
  have h7 : Entails.eval a c337 := h 336 (by decide)
  have h8 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7221 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1579, some c333, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7221 : lratChecker f7221 p7221 = .success := by decide +kernel
theorem unsat7221 : Unsatisfiable (PosFin 65) f7221 := by
  apply lratCheckerSound f7221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7221
  · intro a ha; simp [p7221] at ha; subst a; trivial
  · exact checked7221
theorem derived7221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7221 := by
  apply localUnsat_implies_entails f7221 [c1579, c333] c7221 unsat7221 (by rfl) a
  have h0 : Entails.eval a c1579 := h 1578 (by decide)
  have h1 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7222 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1578, some c1616, some c747, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7222 : lratChecker f7222 p7222 = .success := by decide +kernel
theorem unsat7222 : Unsatisfiable (PosFin 65) f7222 := by
  apply lratCheckerSound f7222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7222
  · intro a ha; simp [p7222] at ha; subst a; trivial
  · exact checked7222
theorem derived7222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7222 := by
  apply localUnsat_implies_entails f7222 [c1578, c1616, c747] c7222 unsat7222 (by rfl) a
  have h0 : Entails.eval a c1578 := h 1577 (by decide)
  have h1 : Entails.eval a c1616 := h 1615 (by decide)
  have h2 : Entails.eval a c747 := h 746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7223 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c7208, some c7220, some c7221, some c7222, some c256, some c1621, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7223 : lratChecker f7223 p7223 = .success := by decide +kernel
theorem unsat7223 : Unsatisfiable (PosFin 65) f7223 := by
  apply lratCheckerSound f7223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7223
  · intro a ha; simp [p7223] at ha; subst a; trivial
  · exact checked7223
theorem derived7223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7223 := by
  apply localUnsat_implies_entails f7223 [c7192, c7208, c7220, c7221, c7222, c256, c1621] c7223 unsat7223 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c7208 := derived7208 a h
  have h2 : Entails.eval a c7220 := derived7220 a h
  have h3 : Entails.eval a c7221 := derived7221 a h
  have h4 : Entails.eval a c7222 := derived7222 a h
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c1621 := h 1620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7224 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1670, some c1679, some c2538, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7224 : lratChecker f7224 p7224 = .success := by decide +kernel
theorem unsat7224 : Unsatisfiable (PosFin 65) f7224 := by
  apply lratCheckerSound f7224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7224
  · intro a ha; simp [p7224] at ha; subst a; trivial
  · exact checked7224
theorem derived7224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7224 := by
  apply localUnsat_implies_entails f7224 [c1670, c1679, c2538] c7224 unsat7224 (by rfl) a
  have h0 : Entails.eval a c1670 := h 1669 (by decide)
  have h1 : Entails.eval a c1679 := h 1678 (by decide)
  have h2 : Entails.eval a c2538 := h 2537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7225 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨31, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c268, some c7224, some c1681, some c1666, some c1381, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7225 : lratChecker f7225 p7225 = .success := by decide +kernel
theorem unsat7225 : Unsatisfiable (PosFin 65) f7225 := by
  apply lratCheckerSound f7225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7225
  · intro a ha; simp [p7225] at ha; subst a; trivial
  · exact checked7225
theorem derived7225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7225 := by
  apply localUnsat_implies_entails f7225 [c268, c7224, c1681, c1666, c1381] c7225 unsat7225 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c7224 := derived7224 a h
  have h2 : Entails.eval a c1681 := h 1680 (by decide)
  have h3 : Entails.eval a c1666 := h 1665 (by decide)
  have h4 : Entails.eval a c1381 := h 1380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7226 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1700, some c1702, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7226 : lratChecker f7226 p7226 = .success := by decide +kernel
theorem unsat7226 : Unsatisfiable (PosFin 65) f7226 := by
  apply lratCheckerSound f7226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7226
  · intro a ha; simp [p7226] at ha; subst a; trivial
  · exact checked7226
theorem derived7226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7226 := by
  apply localUnsat_implies_entails f7226 [c1700, c1702] c7226 unsat7226 (by rfl) a
  have h0 : Entails.eval a c1700 := h 1699 (by decide)
  have h1 : Entails.eval a c1702 := h 1701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7227 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c358, some c359, some c351, some c335, some c7226, some c253, some c7224, some c7225, some c261, some c1666, some c1678, some c1387, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7227 : lratChecker f7227 p7227 = .success := by decide +kernel
theorem unsat7227 : Unsatisfiable (PosFin 65) f7227 := by
  apply lratCheckerSound f7227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7227
  · intro a ha; simp [p7227] at ha; subst a; trivial
  · exact checked7227
theorem derived7227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7227 := by
  apply localUnsat_implies_entails f7227 [c358, c359, c351, c335, c7226, c253, c7224, c7225, c261, c1666, c1678, c1387] c7227 unsat7227 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c7226 := derived7226 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c7224 := derived7224 a h
  have h7 : Entails.eval a c7225 := derived7225 a h
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c1666 := h 1665 (by decide)
  have h10 : Entails.eval a c1678 := h 1677 (by decide)
  have h11 : Entails.eval a c1387 := h 1386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7228 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7226, some c273, some c7224, some c1732, some c2544, some c1197, some c2637, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7228 : lratChecker f7228 p7228 = .success := by decide +kernel
theorem unsat7228 : Unsatisfiable (PosFin 65) f7228 := by
  apply lratCheckerSound f7228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7228
  · intro a ha; simp [p7228] at ha; subst a; trivial
  · exact checked7228
theorem derived7228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7228 := by
  apply localUnsat_implies_entails f7228 [c7226, c273, c7224, c1732, c2544, c1197, c2637] c7228 unsat7228 (by rfl) a
  have h0 : Entails.eval a c7226 := derived7226 a h
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c7224 := derived7224 a h
  have h3 : Entails.eval a c1732 := h 1731 (by decide)
  have h4 : Entails.eval a c2544 := h 2543 (by decide)
  have h5 : Entails.eval a c1197 := h 1196 (by decide)
  have h6 : Entails.eval a c2637 := h 2636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7229 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7228, some c1720, some c275, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7229 : lratChecker f7229 p7229 = .success := by decide +kernel
theorem unsat7229 : Unsatisfiable (PosFin 65) f7229 := by
  apply lratCheckerSound f7229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7229
  · intro a ha; simp [p7229] at ha; subst a; trivial
  · exact checked7229
theorem derived7229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7229 := by
  apply localUnsat_implies_entails f7229 [c7228, c1720, c275] c7229 unsat7229 (by rfl) a
  have h0 : Entails.eval a c7228 := derived7228 a h
  have h1 : Entails.eval a c1720 := h 1719 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7230 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7227, some c7229, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7230 : lratChecker f7230 p7230 = .success := by decide +kernel
theorem unsat7230 : Unsatisfiable (PosFin 65) f7230 := by
  apply lratCheckerSound f7230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7230
  · intro a ha; simp [p7230] at ha; subst a; trivial
  · exact checked7230
theorem derived7230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7230 := by
  apply localUnsat_implies_entails f7230 [c7227, c7229] c7230 unsat7230 (by rfl) a
  have h0 : Entails.eval a c7227 := derived7227 a h
  have h1 : Entails.eval a c7229 := derived7229 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7231 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c358, some c337, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7231 : lratChecker f7231 p7231 = .success := by decide +kernel
theorem unsat7231 : Unsatisfiable (PosFin 65) f7231 := by
  apply lratCheckerSound f7231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7231
  · intro a ha; simp [p7231] at ha; subst a; trivial
  · exact checked7231
theorem derived7231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7231 := by
  apply localUnsat_implies_entails f7231 [c358, c337] c7231 unsat7231 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7232 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c387, some c1686, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7232 : lratChecker f7232 p7232 = .success := by decide +kernel
theorem unsat7232 : Unsatisfiable (PosFin 65) f7232 := by
  apply lratCheckerSound f7232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7232
  · intro a ha; simp [p7232] at ha; subst a; trivial
  · exact checked7232
theorem derived7232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7232 := by
  apply localUnsat_implies_entails f7232 [c387, c1686] c7232 unsat7232 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c1686 := h 1685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7233 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c407, some c1694, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7233 : lratChecker f7233 p7233 = .success := by decide +kernel
theorem unsat7233 : Unsatisfiable (PosFin 65) f7233 := by
  apply lratCheckerSound f7233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7233
  · intro a ha; simp [p7233] at ha; subst a; trivial
  · exact checked7233
theorem derived7233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7233 := by
  apply localUnsat_implies_entails f7233 [c407, c1694] c7233 unsat7233 (by rfl) a
  have h0 : Entails.eval a c407 := h 406 (by decide)
  have h1 : Entails.eval a c1694 := h 1693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7234 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7233, some c7232, some c7197, some c7230, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7234 : lratChecker f7234 p7234 = .success := by decide +kernel
theorem unsat7234 : Unsatisfiable (PosFin 65) f7234 := by
  apply lratCheckerSound f7234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7234
  · intro a ha; simp [p7234] at ha; subst a; trivial
  · exact checked7234
theorem derived7234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7234 := by
  apply localUnsat_implies_entails f7234 [c7233, c7232, c7197, c7230] c7234 unsat7234 (by rfl) a
  have h0 : Entails.eval a c7233 := derived7233 a h
  have h1 : Entails.eval a c7232 := derived7232 a h
  have h2 : Entails.eval a c7197 := derived7197 a h
  have h3 : Entails.eval a c7230 := derived7230 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7235 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7234, some c358, some c359, some c7204, some c7201, some c2183, some c2198, some c1893, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7235 : lratChecker f7235 p7235 = .success := by decide +kernel
theorem unsat7235 : Unsatisfiable (PosFin 65) f7235 := by
  apply lratCheckerSound f7235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7235
  · intro a ha; simp [p7235] at ha; subst a; trivial
  · exact checked7235
theorem derived7235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7235 := by
  apply localUnsat_implies_entails f7235 [c7234, c358, c359, c7204, c7201, c2183, c2198, c1893] c7235 unsat7235 (by rfl) a
  have h0 : Entails.eval a c7234 := derived7234 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c7204 := derived7204 a h
  have h4 : Entails.eval a c7201 := derived7201 a h
  have h5 : Entails.eval a c2183 := h 2182 (by decide)
  have h6 : Entails.eval a c2198 := h 2197 (by decide)
  have h7 : Entails.eval a c1893 := h 1892 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7236 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7204, some c7201, some c1889, some c1908, some c1893, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7236 : lratChecker f7236 p7236 = .success := by decide +kernel
theorem unsat7236 : Unsatisfiable (PosFin 65) f7236 := by
  apply lratCheckerSound f7236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7236
  · intro a ha; simp [p7236] at ha; subst a; trivial
  · exact checked7236
theorem derived7236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7236 := by
  apply localUnsat_implies_entails f7236 [c7204, c7201, c1889, c1908, c1893] c7236 unsat7236 (by rfl) a
  have h0 : Entails.eval a c7204 := derived7204 a h
  have h1 : Entails.eval a c7201 := derived7201 a h
  have h2 : Entails.eval a c1889 := h 1888 (by decide)
  have h3 : Entails.eval a c1908 := h 1907 (by decide)
  have h4 : Entails.eval a c1893 := h 1892 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7237 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c239, some c275, some c1777, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7237 : lratChecker f7237 p7237 = .success := by decide +kernel
theorem unsat7237 : Unsatisfiable (PosFin 65) f7237 := by
  apply lratCheckerSound f7237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7237
  · intro a ha; simp [p7237] at ha; subst a; trivial
  · exact checked7237
theorem derived7237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7237 := by
  apply localUnsat_implies_entails f7237 [c239, c275, c1777] c7237 unsat7237 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c1777 := h 1776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7238 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7234, some c7235, some c7237, some c7236, some c407, some c1808, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7238 : lratChecker f7238 p7238 = .success := by decide +kernel
theorem unsat7238 : Unsatisfiable (PosFin 65) f7238 := by
  apply lratCheckerSound f7238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7238
  · intro a ha; simp [p7238] at ha; subst a; trivial
  · exact checked7238
theorem derived7238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7238 := by
  apply localUnsat_implies_entails f7238 [c7234, c7235, c7237, c7236, c407, c1808] c7238 unsat7238 (by rfl) a
  have h0 : Entails.eval a c7234 := derived7234 a h
  have h1 : Entails.eval a c7235 := derived7235 a h
  have h2 : Entails.eval a c7237 := derived7237 a h
  have h3 : Entails.eval a c7236 := derived7236 a h
  have h4 : Entails.eval a c407 := h 406 (by decide)
  have h5 : Entails.eval a c1808 := h 1807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7239 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1793, some c387, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7239 : lratChecker f7239 p7239 = .success := by decide +kernel
theorem unsat7239 : Unsatisfiable (PosFin 65) f7239 := by
  apply lratCheckerSound f7239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7239
  · intro a ha; simp [p7239] at ha; subst a; trivial
  · exact checked7239
theorem derived7239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7239 := by
  apply localUnsat_implies_entails f7239 [c1793, c387] c7239 unsat7239 (by rfl) a
  have h0 : Entails.eval a c1793 := h 1792 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7240 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7231, some c7239, some c407, some c1808, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7240 : lratChecker f7240 p7240 = .success := by decide +kernel
theorem unsat7240 : Unsatisfiable (PosFin 65) f7240 := by
  apply lratCheckerSound f7240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7240
  · intro a ha; simp [p7240] at ha; subst a; trivial
  · exact checked7240
theorem derived7240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7240 := by
  apply localUnsat_implies_entails f7240 [c7231, c7239, c407, c1808] c7240 unsat7240 (by rfl) a
  have h0 : Entails.eval a c7231 := derived7231 a h
  have h1 : Entails.eval a c7239 := derived7239 a h
  have h2 : Entails.eval a c407 := h 406 (by decide)
  have h3 : Entails.eval a c1808 := h 1807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7241 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7238, some c219, some c251, some c1765, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7241 : lratChecker f7241 p7241 = .success := by decide +kernel
theorem unsat7241 : Unsatisfiable (PosFin 65) f7241 := by
  apply lratCheckerSound f7241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7241
  · intro a ha; simp [p7241] at ha; subst a; trivial
  · exact checked7241
theorem derived7241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7241 := by
  apply localUnsat_implies_entails f7241 [c7238, c219, c251, c1765] c7241 unsat7241 (by rfl) a
  have h0 : Entails.eval a c7238 := derived7238 a h
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c1765 := h 1764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7242 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7240, some c7241, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7242 : lratChecker f7242 p7242 = .success := by decide +kernel
theorem unsat7242 : Unsatisfiable (PosFin 65) f7242 := by
  apply lratCheckerSound f7242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7242
  · intro a ha; simp [p7242] at ha; subst a; trivial
  · exact checked7242
theorem derived7242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7242 := by
  apply localUnsat_implies_entails f7242 [c7240, c7241] c7242 unsat7242 (by rfl) a
  have h0 : Entails.eval a c7240 := derived7240 a h
  have h1 : Entails.eval a c7241 := derived7241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7243 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7242, some c334, some c382, some c1790, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7243 : lratChecker f7243 p7243 = .success := by decide +kernel
theorem unsat7243 : Unsatisfiable (PosFin 65) f7243 := by
  apply lratCheckerSound f7243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7243
  · intro a ha; simp [p7243] at ha; subst a; trivial
  · exact checked7243
theorem derived7243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7243 := by
  apply localUnsat_implies_entails f7243 [c7242, c334, c382, c1790] c7243 unsat7243 (by rfl) a
  have h0 : Entails.eval a c7242 := derived7242 a h
  have h1 : Entails.eval a c334 := h 333 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c1790 := h 1789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7244 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7210, some c1912, some c222, some c1641, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7244 : lratChecker f7244 p7244 = .success := by decide +kernel
theorem unsat7244 : Unsatisfiable (PosFin 65) f7244 := by
  apply lratCheckerSound f7244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7244
  · intro a ha; simp [p7244] at ha; subst a; trivial
  · exact checked7244
theorem derived7244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7244 := by
  apply localUnsat_implies_entails f7244 [c7210, c1912, c222, c1641] c7244 unsat7244 (by rfl) a
  have h0 : Entails.eval a c7210 := derived7210 a h
  have h1 : Entails.eval a c1912 := h 1911 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c1641 := h 1640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7245 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7237, some c7244, some c219, some c251, some c1765, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7245 : lratChecker f7245 p7245 = .success := by decide +kernel
theorem unsat7245 : Unsatisfiable (PosFin 65) f7245 := by
  apply lratCheckerSound f7245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7245
  · intro a ha; simp [p7245] at ha; subst a; trivial
  · exact checked7245
theorem derived7245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7245 := by
  apply localUnsat_implies_entails f7245 [c7237, c7244, c219, c251, c1765] c7245 unsat7245 (by rfl) a
  have h0 : Entails.eval a c7237 := derived7237 a h
  have h1 : Entails.eval a c7244 := derived7244 a h
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c1765 := h 1764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7246 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c330, some c342, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7246 : lratChecker f7246 p7246 = .success := by decide +kernel
theorem unsat7246 : Unsatisfiable (PosFin 65) f7246 := by
  apply lratCheckerSound f7246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7246
  · intro a ha; simp [p7246] at ha; subst a; trivial
  · exact checked7246
theorem derived7246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7246 := by
  apply localUnsat_implies_entails f7246 [c330, c342] c7246 unsat7246 (by rfl) a
  have h0 : Entails.eval a c330 := h 329 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7247 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c259, some c264, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7247 : lratChecker f7247 p7247 = .success := by decide +kernel
theorem unsat7247 : Unsatisfiable (PosFin 65) f7247 := by
  apply lratCheckerSound f7247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7247
  · intro a ha; simp [p7247] at ha; subst a; trivial
  · exact checked7247
theorem derived7247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7247 := by
  apply localUnsat_implies_entails f7247 [c259, c264] c7247 unsat7247 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7248 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨31, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c218, some c397, some c2621, some c2597, some c2151, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7248 : lratChecker f7248 p7248 = .success := by decide +kernel
theorem unsat7248 : Unsatisfiable (PosFin 65) f7248 := by
  apply lratCheckerSound f7248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7248
  · intro a ha; simp [p7248] at ha; subst a; trivial
  · exact checked7248
theorem derived7248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7248 := by
  apply localUnsat_implies_entails f7248 [c218, c397, c2621, c2597, c2151] c7248 unsat7248 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c397 := h 396 (by decide)
  have h2 : Entails.eval a c2621 := h 2620 (by decide)
  have h3 : Entails.eval a c2597 := h 2596 (by decide)
  have h4 : Entails.eval a c2151 := h 2150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7249 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7243, some c7244, some c7245, some c7232, some c7246, some c7247, some c1718, some c1715, some c1717, some c7248, some c390, some c226, some c2600, some c1687, some c2631, some c2164, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7249 : lratChecker f7249 p7249 = .success := by decide +kernel
theorem unsat7249 : Unsatisfiable (PosFin 65) f7249 := by
  apply lratCheckerSound f7249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7249
  · intro a ha; simp [p7249] at ha; subst a; trivial
  · exact checked7249
theorem derived7249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7249 := by
  apply localUnsat_implies_entails f7249 [c7243, c7244, c7245, c7232, c7246, c7247, c1718, c1715, c1717, c7248, c390, c226, c2600, c1687, c2631, c2164] c7249 unsat7249 (by rfl) a
  have h0 : Entails.eval a c7243 := derived7243 a h
  have h1 : Entails.eval a c7244 := derived7244 a h
  have h2 : Entails.eval a c7245 := derived7245 a h
  have h3 : Entails.eval a c7232 := derived7232 a h
  have h4 : Entails.eval a c7246 := derived7246 a h
  have h5 : Entails.eval a c7247 := derived7247 a h
  have h6 : Entails.eval a c1718 := h 1717 (by decide)
  have h7 : Entails.eval a c1715 := h 1714 (by decide)
  have h8 : Entails.eval a c1717 := h 1716 (by decide)
  have h9 : Entails.eval a c7248 := derived7248 a h
  have h10 : Entails.eval a c390 := h 389 (by decide)
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c2600 := h 2599 (by decide)
  have h13 : Entails.eval a c1687 := h 1686 (by decide)
  have h14 : Entails.eval a c2631 := h 2630 (by decide)
  have h15 : Entails.eval a c2164 := h 2163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7250 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1900, some c387, some c1656, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7250 : lratChecker f7250 p7250 = .success := by decide +kernel
theorem unsat7250 : Unsatisfiable (PosFin 65) f7250 := by
  apply lratCheckerSound f7250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7250
  · intro a ha; simp [p7250] at ha; subst a; trivial
  · exact checked7250
theorem derived7250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7250 := by
  apply localUnsat_implies_entails f7250 [c1900, c387, c1656] c7250 unsat7250 (by rfl) a
  have h0 : Entails.eval a c1900 := h 1899 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c1656 := h 1655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7251 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c392, some c379, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7251 : lratChecker f7251 p7251 = .success := by decide +kernel
theorem unsat7251 : Unsatisfiable (PosFin 65) f7251 := by
  apply lratCheckerSound f7251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7251
  · intro a ha; simp [p7251] at ha; subst a; trivial
  · exact checked7251
theorem derived7251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7251 := by
  apply localUnsat_implies_entails f7251 [c392, c379] c7251 unsat7251 (by rfl) a
  have h0 : Entails.eval a c392 := h 391 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7252 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7243, some c7245, some c7244, some c7249, some c7250, some c7246, some c7247, some c7251, some c1794, some c1804, some c1803, some c1813, some c1810, some c7248, some c2003, some c226, some c2600, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7252 : lratChecker f7252 p7252 = .success := by decide +kernel
theorem unsat7252 : Unsatisfiable (PosFin 65) f7252 := by
  apply lratCheckerSound f7252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7252
  · intro a ha; simp [p7252] at ha; subst a; trivial
  · exact checked7252
theorem derived7252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7252 := by
  apply localUnsat_implies_entails f7252 [c7243, c7245, c7244, c7249, c7250, c7246, c7247, c7251, c1794, c1804, c1803, c1813, c1810, c7248, c2003, c226, c2600] c7252 unsat7252 (by rfl) a
  have h0 : Entails.eval a c7243 := derived7243 a h
  have h1 : Entails.eval a c7245 := derived7245 a h
  have h2 : Entails.eval a c7244 := derived7244 a h
  have h3 : Entails.eval a c7249 := derived7249 a h
  have h4 : Entails.eval a c7250 := derived7250 a h
  have h5 : Entails.eval a c7246 := derived7246 a h
  have h6 : Entails.eval a c7247 := derived7247 a h
  have h7 : Entails.eval a c7251 := derived7251 a h
  have h8 : Entails.eval a c1794 := h 1793 (by decide)
  have h9 : Entails.eval a c1804 := h 1803 (by decide)
  have h10 : Entails.eval a c1803 := h 1802 (by decide)
  have h11 : Entails.eval a c1813 := h 1812 (by decide)
  have h12 : Entails.eval a c1810 := h 1809 (by decide)
  have h13 : Entails.eval a c7248 := derived7248 a h
  have h14 : Entails.eval a c2003 := h 2002 (by decide)
  have h15 : Entails.eval a c226 := h 225 (by decide)
  have h16 : Entails.eval a c2600 := h 2599 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7253 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7232, some c250, some c1711, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7253 : lratChecker f7253 p7253 = .success := by decide +kernel
theorem unsat7253 : Unsatisfiable (PosFin 65) f7253 := by
  apply lratCheckerSound f7253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7253
  · intro a ha; simp [p7253] at ha; subst a; trivial
  · exact checked7253
theorem derived7253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7253 := by
  apply localUnsat_implies_entails f7253 [c7232, c250, c1711] c7253 unsat7253 (by rfl) a
  have h0 : Entails.eval a c7232 := derived7232 a h
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c1711 := h 1710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7254 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7243, some c7245, some c7252, some c7253, some c7250, some c7246, some c7251, some c1797, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7254 : lratChecker f7254 p7254 = .success := by decide +kernel
theorem unsat7254 : Unsatisfiable (PosFin 65) f7254 := by
  apply lratCheckerSound f7254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7254
  · intro a ha; simp [p7254] at ha; subst a; trivial
  · exact checked7254
theorem derived7254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7254 := by
  apply localUnsat_implies_entails f7254 [c7243, c7245, c7252, c7253, c7250, c7246, c7251, c1797] c7254 unsat7254 (by rfl) a
  have h0 : Entails.eval a c7243 := derived7243 a h
  have h1 : Entails.eval a c7245 := derived7245 a h
  have h2 : Entails.eval a c7252 := derived7252 a h
  have h3 : Entails.eval a c7253 := derived7253 a h
  have h4 : Entails.eval a c7250 := derived7250 a h
  have h5 : Entails.eval a c7246 := derived7246 a h
  have h6 : Entails.eval a c7251 := derived7251 a h
  have h7 : Entails.eval a c1797 := h 1796 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7255 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c333, some c88, some c1737, some c2045, some c135, some c2645, some c3068, some c6745, some c97, some c85, some c3064, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7255 : lratChecker f7255 p7255 = .success := by decide +kernel
theorem unsat7255 : Unsatisfiable (PosFin 65) f7255 := by
  apply lratCheckerSound f7255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7255
  · intro a ha; simp [p7255] at ha; subst a; trivial
  · exact checked7255
theorem derived7255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7255 := by
  apply localUnsat_implies_entails f7255 [c333, c88, c1737, c2045, c135, c2645, c3068, c6745, c97, c85, c3064] c7255 unsat7255 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c1737 := h 1736 (by decide)
  have h3 : Entails.eval a c2045 := h 2044 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c2645 := h 2644 (by decide)
  have h6 : Entails.eval a c3068 := h 3067 (by decide)
  have h7 : Entails.eval a c6745 := derived6745 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c3064 := h 3063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7256 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1672, some c1684, some c2023, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7256 : lratChecker f7256 p7256 = .success := by decide +kernel
theorem unsat7256 : Unsatisfiable (PosFin 65) f7256 := by
  apply lratCheckerSound f7256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7256
  · intro a ha; simp [p7256] at ha; subst a; trivial
  · exact checked7256
theorem derived7256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7256 := by
  apply localUnsat_implies_entails f7256 [c1672, c1684, c2023] c7256 unsat7256 (by rfl) a
  have h0 : Entails.eval a c1672 := h 1671 (by decide)
  have h1 : Entails.eval a c1684 := h 1683 (by decide)
  have h2 : Entails.eval a c2023 := h 2022 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7257 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c7223, some c7243, some c7245, some c7254, some c7255, some c7244, some c7256, some c1964, some c1760, some c286, some c747, some c786, some c269, some c1796, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7257 : lratChecker f7257 p7257 = .success := by decide +kernel
theorem unsat7257 : Unsatisfiable (PosFin 65) f7257 := by
  apply lratCheckerSound f7257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7257
  · intro a ha; simp [p7257] at ha; subst a; trivial
  · exact checked7257
theorem derived7257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7257 := by
  apply localUnsat_implies_entails f7257 [c7192, c7223, c7243, c7245, c7254, c7255, c7244, c7256, c1964, c1760, c286, c747, c786, c269, c1796] c7257 unsat7257 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c7223 := derived7223 a h
  have h2 : Entails.eval a c7243 := derived7243 a h
  have h3 : Entails.eval a c7245 := derived7245 a h
  have h4 : Entails.eval a c7254 := derived7254 a h
  have h5 : Entails.eval a c7255 := derived7255 a h
  have h6 : Entails.eval a c7244 := derived7244 a h
  have h7 : Entails.eval a c7256 := derived7256 a h
  have h8 : Entails.eval a c1964 := h 1963 (by decide)
  have h9 : Entails.eval a c1760 := h 1759 (by decide)
  have h10 : Entails.eval a c286 := h 285 (by decide)
  have h11 : Entails.eval a c747 := h 746 (by decide)
  have h12 : Entails.eval a c786 := h 785 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c1796 := h 1795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7258 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c253, some c803, some c795, some c331, some c353, some c268, some c408, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7258 : lratChecker f7258 p7258 = .success := by decide +kernel
theorem unsat7258 : Unsatisfiable (PosFin 65) f7258 := by
  apply lratCheckerSound f7258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7258
  · intro a ha; simp [p7258] at ha; subst a; trivial
  · exact checked7258
theorem derived7258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7258 := by
  apply localUnsat_implies_entails f7258 [c253, c803, c795, c331, c353, c268, c408] c7258 unsat7258 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c803 := h 802 (by decide)
  have h2 : Entails.eval a c795 := h 794 (by decide)
  have h3 : Entails.eval a c331 := h 330 (by decide)
  have h4 : Entails.eval a c353 := h 352 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c408 := h 407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7259 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1611, some c1613, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7259 : lratChecker f7259 p7259 = .success := by decide +kernel
theorem unsat7259 : Unsatisfiable (PosFin 65) f7259 := by
  apply lratCheckerSound f7259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7259
  · intro a ha; simp [p7259] at ha; subst a; trivial
  · exact checked7259
theorem derived7259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7259 := by
  apply localUnsat_implies_entails f7259 [c1611, c1613] c7259 unsat7259 (by rfl) a
  have h0 : Entails.eval a c1611 := h 1610 (by decide)
  have h1 : Entails.eval a c1613 := h 1612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7260 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c335, some c361, some c351, some c7259, some c253, some c7258, some c1678, some c1680, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7260 : lratChecker f7260 p7260 = .success := by decide +kernel
theorem unsat7260 : Unsatisfiable (PosFin 65) f7260 := by
  apply lratCheckerSound f7260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7260
  · intro a ha; simp [p7260] at ha; subst a; trivial
  · exact checked7260
theorem derived7260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7260 := by
  apply localUnsat_implies_entails f7260 [c335, c361, c351, c7259, c253, c7258, c1678, c1680] c7260 unsat7260 (by rfl) a
  have h0 : Entails.eval a c335 := h 334 (by decide)
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c7259 := derived7259 a h
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c7258 := derived7258 a h
  have h6 : Entails.eval a c1678 := h 1677 (by decide)
  have h7 : Entails.eval a c1680 := h 1679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7261 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7260, some c1566, some c1581, some c1571, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7261 : lratChecker f7261 p7261 = .success := by decide +kernel
theorem unsat7261 : Unsatisfiable (PosFin 65) f7261 := by
  apply lratCheckerSound f7261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7261
  · intro a ha; simp [p7261] at ha; subst a; trivial
  · exact checked7261
theorem derived7261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7261 := by
  apply localUnsat_implies_entails f7261 [c7260, c1566, c1581, c1571] c7261 unsat7261 (by rfl) a
  have h0 : Entails.eval a c7260 := derived7260 a h
  have h1 : Entails.eval a c1566 := h 1565 (by decide)
  have h2 : Entails.eval a c1581 := h 1580 (by decide)
  have h3 : Entails.eval a c1571 := h 1570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7262 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c366, some c363, some c356, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7262 : lratChecker f7262 p7262 = .success := by decide +kernel
theorem unsat7262 : Unsatisfiable (PosFin 65) f7262 := by
  apply lratCheckerSound f7262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7262
  · intro a ha; simp [p7262] at ha; subst a; trivial
  · exact checked7262
theorem derived7262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7262 := by
  apply localUnsat_implies_entails f7262 [c366, c363, c356] c7262 unsat7262 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7263 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7262, some c1602, some c1605, some c1596, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7263 : lratChecker f7263 p7263 = .success := by decide +kernel
theorem unsat7263 : Unsatisfiable (PosFin 65) f7263 := by
  apply lratCheckerSound f7263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7263
  · intro a ha; simp [p7263] at ha; subst a; trivial
  · exact checked7263
theorem derived7263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7263 := by
  apply localUnsat_implies_entails f7263 [c7262, c1602, c1605, c1596] c7263 unsat7263 (by rfl) a
  have h0 : Entails.eval a c7262 := derived7262 a h
  have h1 : Entails.eval a c1602 := h 1601 (by decide)
  have h2 : Entails.eval a c1605 := h 1604 (by decide)
  have h3 : Entails.eval a c1596 := h 1595 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7264 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7263, some c7261, some c335, some c361, some c351, some c7259, some c253, some c767, some c331, some c247, some c268, some c353, some c237, some c7201, some c2183, some c2190, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7264 : lratChecker f7264 p7264 = .success := by decide +kernel
theorem unsat7264 : Unsatisfiable (PosFin 65) f7264 := by
  apply lratCheckerSound f7264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7264
  · intro a ha; simp [p7264] at ha; subst a; trivial
  · exact checked7264
theorem derived7264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7264 := by
  apply localUnsat_implies_entails f7264 [c7263, c7261, c335, c361, c351, c7259, c253, c767, c331, c247, c268, c353, c237, c7201, c2183, c2190] c7264 unsat7264 (by rfl) a
  have h0 : Entails.eval a c7263 := derived7263 a h
  have h1 : Entails.eval a c7261 := derived7261 a h
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c361 := h 360 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c7259 := derived7259 a h
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c767 := h 766 (by decide)
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c7201 := derived7201 a h
  have h14 : Entails.eval a c2183 := h 2182 (by decide)
  have h15 : Entails.eval a c2190 := h 2189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7265 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7263, some c7264, some c1566, some c1581, some c1571, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7265 : lratChecker f7265 p7265 = .success := by decide +kernel
theorem unsat7265 : Unsatisfiable (PosFin 65) f7265 := by
  apply lratCheckerSound f7265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7265
  · intro a ha; simp [p7265] at ha; subst a; trivial
  · exact checked7265
theorem derived7265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7265 := by
  apply localUnsat_implies_entails f7265 [c7263, c7264, c1566, c1581, c1571] c7265 unsat7265 (by rfl) a
  have h0 : Entails.eval a c7263 := derived7263 a h
  have h1 : Entails.eval a c7264 := derived7264 a h
  have h2 : Entails.eval a c1566 := h 1565 (by decide)
  have h3 : Entails.eval a c1581 := h 1580 (by decide)
  have h4 : Entails.eval a c1571 := h 1570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7266 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1583, some c337, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7266 : lratChecker f7266 p7266 = .success := by decide +kernel
theorem unsat7266 : Unsatisfiable (PosFin 65) f7266 := by
  apply lratCheckerSound f7266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7266
  · intro a ha; simp [p7266] at ha; subst a; trivial
  · exact checked7266
theorem derived7266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7266 := by
  apply localUnsat_implies_entails f7266 [c1583, c337] c7266 unsat7266 (by rfl) a
  have h0 : Entails.eval a c1583 := h 1582 (by decide)
  have h1 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7267 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c252, some c1619, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7267 : lratChecker f7267 p7267 = .success := by decide +kernel
theorem unsat7267 : Unsatisfiable (PosFin 65) f7267 := by
  apply lratCheckerSound f7267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7267
  · intro a ha; simp [p7267] at ha; subst a; trivial
  · exact checked7267
theorem derived7267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7267 := by
  apply localUnsat_implies_entails f7267 [c252, c1619] c7267 unsat7267 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c1619 := h 1618 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7268 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7263, some c7266, some c7265, some c7267, some c1581, some c335, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7268 : lratChecker f7268 p7268 = .success := by decide +kernel
theorem unsat7268 : Unsatisfiable (PosFin 65) f7268 := by
  apply lratCheckerSound f7268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7268
  · intro a ha; simp [p7268] at ha; subst a; trivial
  · exact checked7268
theorem derived7268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7268 := by
  apply localUnsat_implies_entails f7268 [c7263, c7266, c7265, c7267, c1581, c335] c7268 unsat7268 (by rfl) a
  have h0 : Entails.eval a c7263 := derived7263 a h
  have h1 : Entails.eval a c7266 := derived7266 a h
  have h2 : Entails.eval a c7265 := derived7265 a h
  have h3 : Entails.eval a c7267 := derived7267 a h
  have h4 : Entails.eval a c1581 := h 1580 (by decide)
  have h5 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7269 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c351, some c335, some c253, some c7258, some c1678, some c1680, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7269 : lratChecker f7269 p7269 = .success := by decide +kernel
theorem unsat7269 : Unsatisfiable (PosFin 65) f7269 := by
  apply lratCheckerSound f7269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7269
  · intro a ha; simp [p7269] at ha; subst a; trivial
  · exact checked7269
theorem derived7269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7269 := by
  apply localUnsat_implies_entails f7269 [c351, c335, c253, c7258, c1678, c1680] c7269 unsat7269 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c335 := h 334 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c7258 := derived7258 a h
  have h4 : Entails.eval a c1678 := h 1677 (by decide)
  have h5 : Entails.eval a c1680 := h 1679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7270 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7269, some c1705, some c1713, some c1703, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7270 : lratChecker f7270 p7270 = .success := by decide +kernel
theorem unsat7270 : Unsatisfiable (PosFin 65) f7270 := by
  apply lratCheckerSound f7270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7270
  · intro a ha; simp [p7270] at ha; subst a; trivial
  · exact checked7270
theorem derived7270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7270 := by
  apply localUnsat_implies_entails f7270 [c7269, c1705, c1713, c1703] c7270 unsat7270 (by rfl) a
  have h0 : Entails.eval a c7269 := derived7269 a h
  have h1 : Entails.eval a c1705 := h 1704 (by decide)
  have h2 : Entails.eval a c1713 := h 1712 (by decide)
  have h3 : Entails.eval a c1703 := h 1702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7271 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c253, some c7258, some c767, some c7135, some c331, some c1661, some c1652, some c1651, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7271 : lratChecker f7271 p7271 = .success := by decide +kernel
theorem unsat7271 : Unsatisfiable (PosFin 65) f7271 := by
  apply lratCheckerSound f7271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7271
  · intro a ha; simp [p7271] at ha; subst a; trivial
  · exact checked7271
theorem derived7271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7271 := by
  apply localUnsat_implies_entails f7271 [c253, c7258, c767, c7135, c331, c1661, c1652, c1651] c7271 unsat7271 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c7258 := derived7258 a h
  have h2 : Entails.eval a c767 := h 766 (by decide)
  have h3 : Entails.eval a c7135 := derived7135 a h
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c1661 := h 1660 (by decide)
  have h6 : Entails.eval a c1652 := h 1651 (by decide)
  have h7 : Entails.eval a c1651 := h 1650 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7272 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1756, some c2061, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7272 : lratChecker f7272 p7272 = .success := by decide +kernel
theorem unsat7272 : Unsatisfiable (PosFin 65) f7272 := by
  apply lratCheckerSound f7272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7272
  · intro a ha; simp [p7272] at ha; subst a; trivial
  · exact checked7272
theorem derived7272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7272 := by
  apply localUnsat_implies_entails f7272 [c1756, c2061] c7272 unsat7272 (by rfl) a
  have h0 : Entails.eval a c1756 := h 1755 (by decide)
  have h1 : Entails.eval a c2061 := h 2060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7273 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1032, some c1752, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7273 : lratChecker f7273 p7273 = .success := by decide +kernel
theorem unsat7273 : Unsatisfiable (PosFin 65) f7273 := by
  apply lratCheckerSound f7273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7273
  · intro a ha; simp [p7273] at ha; subst a; trivial
  · exact checked7273
theorem derived7273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7273 := by
  apply localUnsat_implies_entails f7273 [c1032, c1752] c7273 unsat7273 (by rfl) a
  have h0 : Entails.eval a c1032 := h 1031 (by decide)
  have h1 : Entails.eval a c1752 := h 1751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7274 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7268, some c335, some c361, some c351, some c7270, some c7271, some c7273, some c1470, some c1507, some c2675, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7274 : lratChecker f7274 p7274 = .success := by decide +kernel
theorem unsat7274 : Unsatisfiable (PosFin 65) f7274 := by
  apply lratCheckerSound f7274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7274
  · intro a ha; simp [p7274] at ha; subst a; trivial
  · exact checked7274
theorem derived7274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7274 := by
  apply localUnsat_implies_entails f7274 [c7268, c335, c361, c351, c7270, c7271, c7273, c1470, c1507, c2675] c7274 unsat7274 (by rfl) a
  have h0 : Entails.eval a c7268 := derived7268 a h
  have h1 : Entails.eval a c335 := h 334 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c7270 := derived7270 a h
  have h5 : Entails.eval a c7271 := derived7271 a h
  have h6 : Entails.eval a c7273 := derived7273 a h
  have h7 : Entails.eval a c1470 := h 1469 (by decide)
  have h8 : Entails.eval a c1507 := h 1506 (by decide)
  have h9 : Entails.eval a c2675 := h 2674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7275 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1783, some c2650, some c1172, some c2641, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7275 : lratChecker f7275 p7275 = .success := by decide +kernel
theorem unsat7275 : Unsatisfiable (PosFin 65) f7275 := by
  apply lratCheckerSound f7275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7275
  · intro a ha; simp [p7275] at ha; subst a; trivial
  · exact checked7275
theorem derived7275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7275 := by
  apply localUnsat_implies_entails f7275 [c1783, c2650, c1172, c2641] c7275 unsat7275 (by rfl) a
  have h0 : Entails.eval a c1783 := h 1782 (by decide)
  have h1 : Entails.eval a c2650 := h 2649 (by decide)
  have h2 : Entails.eval a c1172 := h 1171 (by decide)
  have h3 : Entails.eval a c2641 := h 2640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7276 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1666, some c2544, some c1197, some c2637, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7276 : lratChecker f7276 p7276 = .success := by decide +kernel
theorem unsat7276 : Unsatisfiable (PosFin 65) f7276 := by
  apply lratCheckerSound f7276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7276
  · intro a ha; simp [p7276] at ha; subst a; trivial
  · exact checked7276
theorem derived7276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7276 := by
  apply localUnsat_implies_entails f7276 [c1666, c2544, c1197, c2637] c7276 unsat7276 (by rfl) a
  have h0 : Entails.eval a c1666 := h 1665 (by decide)
  have h1 : Entails.eval a c2544 := h 2543 (by decide)
  have h2 : Entails.eval a c1197 := h 1196 (by decide)
  have h3 : Entails.eval a c2637 := h 2636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7277 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c253, some c7276, some c1785, some c2651, some c383, some c1384, some c2524, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7277 : lratChecker f7277 p7277 = .success := by decide +kernel
theorem unsat7277 : Unsatisfiable (PosFin 65) f7277 := by
  apply lratCheckerSound f7277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7277
  · intro a ha; simp [p7277] at ha; subst a; trivial
  · exact checked7277
theorem derived7277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7277 := by
  apply localUnsat_implies_entails f7277 [c253, c7276, c1785, c2651, c383, c1384, c2524] c7277 unsat7277 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c7276 := derived7276 a h
  have h2 : Entails.eval a c1785 := h 1784 (by decide)
  have h3 : Entails.eval a c2651 := h 2650 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c1384 := h 1383 (by decide)
  have h6 : Entails.eval a c2524 := h 2523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7278 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1739, some c383, some c1937, some c1655, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7278 : lratChecker f7278 p7278 = .success := by decide +kernel
theorem unsat7278 : Unsatisfiable (PosFin 65) f7278 := by
  apply lratCheckerSound f7278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7278
  · intro a ha; simp [p7278] at ha; subst a; trivial
  · exact checked7278
theorem derived7278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7278 := by
  apply localUnsat_implies_entails f7278 [c1739, c383, c1937, c1655] c7278 unsat7278 (by rfl) a
  have h0 : Entails.eval a c1739 := h 1738 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c1937 := h 1936 (by decide)
  have h3 : Entails.eval a c1655 := h 1654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7279 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7277, some c279, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7279 : lratChecker f7279 p7279 = .success := by decide +kernel
theorem unsat7279 : Unsatisfiable (PosFin 65) f7279 := by
  apply lratCheckerSound f7279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7279
  · intro a ha; simp [p7279] at ha; subst a; trivial
  · exact checked7279
theorem derived7279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7279 := by
  apply localUnsat_implies_entails f7279 [c7277, c279] c7279 unsat7279 (by rfl) a
  have h0 : Entails.eval a c7277 := derived7277 a h
  have h1 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7280 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7278, some c7279, some c1699, some c7272, some c1783, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7280 : lratChecker f7280 p7280 = .success := by decide +kernel
theorem unsat7280 : Unsatisfiable (PosFin 65) f7280 := by
  apply lratCheckerSound f7280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7280
  · intro a ha; simp [p7280] at ha; subst a; trivial
  · exact checked7280
theorem derived7280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7280 := by
  apply localUnsat_implies_entails f7280 [c7278, c7279, c1699, c7272, c1783] c7280 unsat7280 (by rfl) a
  have h0 : Entails.eval a c7278 := derived7278 a h
  have h1 : Entails.eval a c7279 := derived7279 a h
  have h2 : Entails.eval a c1699 := h 1698 (by decide)
  have h3 : Entails.eval a c7272 := derived7272 a h
  have h4 : Entails.eval a c1783 := h 1782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7280

end CochromaticTwenty.Certificates.FixedCore1
