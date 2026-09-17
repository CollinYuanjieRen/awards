import MerLeanExperiment.Certificates.B16_4_2.Steps0800_0899

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1284 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1284 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c319, some c57, some c56, some c282, some c105, some c1197, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1284 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1284 : lratChecker f1284 p1284 = .success := by decide +kernel
theorem unsat1284 : Unsatisfiable (PosFin 57) f1284 := by
  apply lratCheckerSound f1284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1284
  · intro a ha; simp [p1284] at ha; subst a; trivial
  · exact checked1284
theorem derived1284 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1284 := by
  apply localUnsat_implies_entails f1284 [c316, c319, c57, c56, c282, c105, c1197] c1284 unsat1284 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1197 := derived1197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1285 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1285 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1283, some c314, some c146, some c315, some c48, some c40, some c60, some c356, some c342, some c19, some c66, some c46, some c2, some c105, some c1187, some c631, some c28, some c212, some c271, some c33, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1285 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1285 : lratChecker f1285 p1285 = .success := by decide +kernel
theorem unsat1285 : Unsatisfiable (PosFin 57) f1285 := by
  apply lratCheckerSound f1285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1285
  · intro a ha; simp [p1285] at ha; subst a; trivial
  · exact checked1285
theorem derived1285 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1285 := by
  apply localUnsat_implies_entails f1285 [c1282, c1283, c314, c146, c315, c48, c40, c60, c356, c342, c19, c66, c46, c2, c105, c1187, c631, c28, c212, c271, c33] c1285 unsat1285 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1283 := derived1283 a h
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c342 := h 341 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c46 := h 45 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c1187 := derived1187 a h
  have h16 : Entails.eval a c631 := derived631 a h
  have h17 : Entails.eval a c28 := h 27 (by decide)
  have h18 : Entails.eval a c212 := h 211 (by decide)
  have h19 : Entails.eval a c271 := h 270 (by decide)
  have h20 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1286 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1286 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1283, some c1278, some c315, some c314, some c1285, some c1284, some c39, some c47, some c356, some c360, some c341, some c347, some c20, some c67, some c282, some c46, some c97, some c105, some c220, some c214, some c28, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1286 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1286 : lratChecker f1286 p1286 = .success := by decide +kernel
theorem unsat1286 : Unsatisfiable (PosFin 57) f1286 := by
  apply lratCheckerSound f1286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1286
  · intro a ha; simp [p1286] at ha; subst a; trivial
  · exact checked1286
theorem derived1286 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1286 := by
  apply localUnsat_implies_entails f1286 [c1282, c1283, c1278, c315, c314, c1285, c1284, c39, c47, c356, c360, c341, c347, c20, c67, c282, c46, c97, c105, c220, c214, c28] c1286 unsat1286 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1283 := derived1283 a h
  have h2 : Entails.eval a c1278 := derived1278 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c1285 := derived1285 a h
  have h6 : Entails.eval a c1284 := derived1284 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c360 := h 359 (by decide)
  have h11 : Entails.eval a c341 := h 340 (by decide)
  have h12 : Entails.eval a c347 := h 346 (by decide)
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c282 := h 281 (by decide)
  have h16 : Entails.eval a c46 := h 45 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c220 := h 219 (by decide)
  have h20 : Entails.eval a c214 := h 213 (by decide)
  have h21 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1287 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1287 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1283, some c38, some c18, some c216, some c33, some c31, some c268, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1287 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1287 : lratChecker f1287 p1287 = .success := by decide +kernel
theorem unsat1287 : Unsatisfiable (PosFin 57) f1287 := by
  apply lratCheckerSound f1287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1287
  · intro a ha; simp [p1287] at ha; subst a; trivial
  · exact checked1287
theorem derived1287 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1287 := by
  apply localUnsat_implies_entails f1287 [c1283, c38, c18, c216, c33, c31, c268] c1287 unsat1287 (by rfl) a
  have h0 : Entails.eval a c1283 := derived1283 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1288 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1288 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1287, some c1274, some c1283, some c1278, some c1286, some c355, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1288 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1288 : lratChecker f1288 p1288 = .success := by decide +kernel
theorem unsat1288 : Unsatisfiable (PosFin 57) f1288 := by
  apply lratCheckerSound f1288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1288
  · intro a ha; simp [p1288] at ha; subst a; trivial
  · exact checked1288
theorem derived1288 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1288 := by
  apply localUnsat_implies_entails f1288 [c1282, c1287, c1274, c1283, c1278, c1286, c355] c1288 unsat1288 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c1274 := derived1274 a h
  have h3 : Entails.eval a c1283 := derived1283 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c1286 := derived1286 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1289 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1287, some c1288, some c1199, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 57) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c1282, c1287, c1288, c1199] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c1288 := derived1288 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c167, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 57) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c667, c167] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1291 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c22, some c658, some c40, some c60, some c356, some c582, some c1183, some c115, some c205, some c145, some c271, some c731, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 57) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c42, c22, c658, c40, c60, c356, c582, c1183, c115, c205, c145, c271, c731] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c658 := derived658 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c582 := derived582 a h
  have h7 : Entails.eval a c1183 := derived1183 a h
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c731 := derived731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1077, some c1282, some c5, some c1290, some c358, some c22, some c76, some c42, some c355, some c1291, some c20, some c32, some c356, some c582, some c115, some c205, some c272, some c731, some c1095, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 57) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c108, c1077, c1282, c5, c1290, c358, c22, c76, c42, c355, c1291, c20, c32, c356, c582, c115, c205, c272, c731, c1095] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c1290 := derived1290 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c1291 := derived1291 a h
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c582 := derived582 a h
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c731 := derived731 a h
  have h19 : Entails.eval a c1095 := derived1095 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1293 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨38, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c658, some c638, some c40, some c115, some c356, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 57) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c658, c638, c40, c115, c356] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c658 := derived658 a h
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1290, some c358, some c22, some c1293, some c20, some c32, some c356, some c115, some c676, some c272, some c270, some c132, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 57) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c1290, c358, c22, c1293, c20, c32, c356, c115, c676, c272, c270, c132] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c1290 := derived1290 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1293 := derived1293 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c676 := derived676 a h
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c22, some c76, some c42, some c269, some c854, some c1238, some c355, some c266, some c782, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 57) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c1282, c22, c76, c42, c269, c854, c1238, c355, c266, c782] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c854 := derived854 a h
  have h6 : Entails.eval a c1238 := derived1238 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c782 := derived782 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1292, some c638, some c1282, some c1077, some c108, some c1294, some c1295, some c358, some c357, some c120, some c171, some c72, some c353, some c782, some c266, some c267, some c36, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 57) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c1292, c638, c1282, c1077, c108, c1294, c1295, c358, c357, c120, c171, c72, c353, c782, c266, c267, c36] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c1292 := derived1292 a h
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1294 := derived1294 a h
  have h6 : Entails.eval a c1295 := derived1295 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c782 := derived782 a h
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1077, some c1282, some c1296, some c356, some c667, some c40, some c358, some c658, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 57) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c108, c1077, c1282, c1296, c356, c667, c40, c358, c658] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1296 := derived1296 a h
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c658 := derived658 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1298 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c108, some c1077, some c1282, some c4, some c1, some c1292, some c1294, some c1297, some c20, some c32, some c356, some c357, some c22, some c76, some c42, some c783, some c854, some c355, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 57) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c112, c108, c1077, c1282, c4, c1, c1292, c1294, c1297, c20, c32, c356, c357, c22, c76, c42, c783, c854, c355] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1292 := derived1292 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c1297 := derived1297 a h
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c783 := derived783 a h
  have h17 : Entails.eval a c854 := derived854 a h
  have h18 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c22, some c76, some c42, some c210, some c899, some c141, some c355, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 57) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c631, c22, c76, c42, c210, c899, c141, c355] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c210 := h 209 (by decide)
  have h5 : Entails.eval a c899 := derived899 a h
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1299, some c358, some c357, some c148, some c120, some c171, some c72, some c212, some c353, some c141, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 57) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c631, c1299, c358, c357, c148, c120, c171, c72, c212, c353, c141] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c108, some c1282, some c22, some c76, some c42, some c210, some c141, some c149, some c355, some c353, some c317, some c318, some c215, some c283, some c1092, some c48, some c151, some c122, some c944, some c32, some c261, some c193, some c81, some c291, some c366, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 57) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c631, c108, c1282, c22, c76, c42, c210, c141, c149, c355, c353, c317, c318, c215, c283, c1092, c48, c151, c122, c944, c32, c261, c193, c81, c291, c366] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c215 := h 214 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c1092 := derived1092 a h
  have h16 : Entails.eval a c48 := h 47 (by decide)
  have h17 : Entails.eval a c151 := h 150 (by decide)
  have h18 : Entails.eval a c122 := h 121 (by decide)
  have h19 : Entails.eval a c944 := derived944 a h
  have h20 : Entails.eval a c32 := h 31 (by decide)
  have h21 : Entails.eval a c261 := h 260 (by decide)
  have h22 : Entails.eval a c193 := h 192 (by decide)
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c291 := h 290 (by decide)
  have h25 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c145, some c117, some c220, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 57) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c145, c117, c220] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1303 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c266, some c36, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 57) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c267, c266, c36] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c108, some c1077, some c1300, some c8, some c1301, some c358, some c357, some c40, some c20, some c72, some c638, some c1302, some c231, some c360, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 57) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c1282, c631, c1303, c108, c1077, c1300, c8, c1301, c358, c357, c40, c20, c72, c638, c1302, c231, c360] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1300 := derived1300 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c1301 := derived1301 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c638 := derived638 a h
  have h14 : Entails.eval a c1302 := derived1302 a h
  have h15 : Entails.eval a c231 := h 230 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨10, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨20, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨34, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1303, some c360, some c1092, some c235, some c36, some c271, some c269, some c123, some c122, some c325, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 57) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1303, c360, c1092, c235, c36, c271, c269, c123, c122, c325] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1303 := derived1303 a h
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c1092 := derived1092 a h
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨20, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c112, some c1303, some c108, some c1077, some c358, some c357, some c120, some c40, some c72, some c8, some c1305, some c231, some c1221, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 57) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c1282, c112, c1303, c108, c1077, c358, c357, c120, c40, c72, c8, c1305, c231, c1221] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c1305 := derived1305 a h
  have h12 : Entails.eval a c231 := h 230 (by decide)
  have h13 : Entails.eval a c1221 := derived1221 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1299, some c1301, some c8, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 57) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c1282, c1299, c1301, c8] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c1301 := derived1301 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c108, some c1077, some c1298, some c631, some c1304, some c10, some c1307, some c357, some c1306, some c20, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 57) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c112, c108, c1077, c1298, c631, c1304, c10, c1307, c357, c1306, c20] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1298 := derived1298 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1304 := derived1304 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c1307 := derived1307 a h
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c1306 := derived1306 a h
  have h10 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1282, some c1077, some c1199, some c42, some c1037, some c76, some c22, some c631, some c1299, some c1301, some c1303, some c210, some c5, some c206, some c24, some c843, some c166, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 57) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c108, c1282, c1077, c1199, c42, c1037, c76, c22, c631, c1299, c1301, c1303, c210, c5, c206, c24, c843, c166] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1199 := derived1199 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c1037 := derived1037 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c631 := derived631 a h
  have h9 : Entails.eval a c1299 := derived1299 a h
  have h10 : Entails.eval a c1301 := derived1301 a h
  have h11 : Entails.eval a c1303 := derived1303 a h
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c843 := derived843 a h
  have h17 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c1282, some c1077, some c108, some c1308, some c1199, some c76, some c22, some c42, some c1309, some c854, some c355, some c1297, some c658, some c202, some c61, some c865, some c314, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 57) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c112, c1282, c1077, c108, c1308, c1199, c76, c22, c42, c1309, c854, c355, c1297, c658, c202, c61, c865, c314] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1308 := derived1308 a h
  have h5 : Entails.eval a c1199 := derived1199 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1309 := derived1309 a h
  have h10 : Entails.eval a c854 := derived854 a h
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c1297 := derived1297 a h
  have h13 : Entails.eval a c658 := derived658 a h
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c865 := derived865 a h
  have h17 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1311 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1077, some c108, some c1308, some c1199, some c42, some c112, some c76, some c22, some c1309, some c854, some c355, some c1310, some c20, some c33, some c32, some c356, some c223, some c783, some c115, some c143, some c52, some c219, some c352, some c51, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1311 : lratChecker f1311 p1311 = .success := by decide +kernel
theorem unsat1311 : Unsatisfiable (PosFin 57) f1311 := by
  apply lratCheckerSound f1311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1311
  · intro a ha; simp [p1311] at ha; subst a; trivial
  · exact checked1311
theorem derived1311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1311 := by
  apply localUnsat_implies_entails f1311 [c1282, c1077, c108, c1308, c1199, c42, c112, c76, c22, c1309, c854, c355, c1310, c20, c33, c32, c356, c223, c783, c115, c143, c52, c219, c352, c51] c1311 unsat1311 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1308 := derived1308 a h
  have h4 : Entails.eval a c1199 := derived1199 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c1309 := derived1309 a h
  have h10 : Entails.eval a c854 := derived854 a h
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c1310 := derived1310 a h
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c223 := h 222 (by decide)
  have h18 : Entails.eval a c783 := derived783 a h
  have h19 : Entails.eval a c115 := h 114 (by decide)
  have h20 : Entails.eval a c143 := h 142 (by decide)
  have h21 : Entails.eval a c52 := h 51 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  have h23 : Entails.eval a c352 := h 351 (by decide)
  have h24 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1312 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1077, some c1282, some c112, some c1308, some c1199, some c22, some c76, some c42, some c1311, some c1, some c631, some c1303, some c210, some c24, some c141, some c355, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1312 : lratChecker f1312 p1312 = .success := by decide +kernel
theorem unsat1312 : Unsatisfiable (PosFin 57) f1312 := by
  apply lratCheckerSound f1312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1312
  · intro a ha; simp [p1312] at ha; subst a; trivial
  · exact checked1312
theorem derived1312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1312 := by
  apply localUnsat_implies_entails f1312 [c108, c1077, c1282, c112, c1308, c1199, c22, c76, c42, c1311, c1, c631, c1303, c210, c24, c141, c355] c1312 unsat1312 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1308 := derived1308 a h
  have h5 : Entails.eval a c1199 := derived1199 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1311 := derived1311 a h
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c631 := derived631 a h
  have h12 : Entails.eval a c1303 := derived1303 a h
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1313 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1304, some c1309, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1313 : lratChecker f1313 p1313 = .success := by decide +kernel
theorem unsat1313 : Unsatisfiable (PosFin 57) f1313 := by
  apply lratCheckerSound f1313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1313
  · intro a ha; simp [p1313] at ha; subst a; trivial
  · exact checked1313
theorem derived1313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1313 := by
  apply localUnsat_implies_entails f1313 [c1304, c1309] c1313 unsat1313 (by rfl) a
  have h0 : Entails.eval a c1304 := derived1304 a h
  have h1 : Entails.eval a c1309 := derived1309 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1314 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1313, some c1312, some c108, some c1077, some c1282, some c1292, some c1297, some c1294, some c20, some c32, some c356, some c357, some c22, some c76, some c42, some c74, some c783, some c353, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 57) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c1313, c1312, c108, c1077, c1282, c1292, c1297, c1294, c20, c32, c356, c357, c22, c76, c42, c74, c783, c353] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c1313 := derived1313 a h
  have h1 : Entails.eval a c1312 := derived1312 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1292 := derived1292 a h
  have h6 : Entails.eval a c1297 := derived1297 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c783 := derived783 a h
  have h17 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1312, some c108, some c1077, some c1282, some c1313, some c1314, some c202, some c4, some c1199, some c22, some c76, some c42, some c74, some c353, some c360, some c865, some c166, some c210, some c782, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 57) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c1312, c108, c1077, c1282, c1313, c1314, c202, c4, c1199, c22, c76, c42, c74, c353, c360, c865, c166, c210, c782] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c1312 := derived1312 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1313 := derived1313 a h
  have h5 : Entails.eval a c1314 := derived1314 a h
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c1199 := derived1199 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c865 := derived865 a h
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c782 := derived782 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c235, some c220, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 57) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c41, c235, c220] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c235 := h 234 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c357, some c40, some c20, some c72, some c1316, some c353, some c360, some c163, some c162, some c207, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p1317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 57) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c358, c357, c40, c20, c72, c1316, c353, c360, c163, c162, c207] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c1316 := derived1316 a h
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c360 := h 359 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1303, some c1317, some c22, some c76, some c42, some c74, some c210, some c353, some c141, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 57) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c631, c1303, c1317, c22, c76, c42, c74, c210, c353, c141] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c1317 := derived1317 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c357, some c40, some c20, some c169, some c72, some c207, some c167, some c360, some c41, some c1095, some c220, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c358, c357, c40, c20, c169, c72, c207, c167, c360, c41, c1095, c220] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c360 := h 359 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c1095 := derived1095 a h
  have h11 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨38, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c22, some c658, some c48, some c40, some c261, some c348, some c102, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c74, c22, c658, c48, c40, c261, c348, c102] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c658 := derived658 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨20, by decide⟩, true), (⟨37, by decide⟩, false), (⟨30, by decide⟩, false), (⟨39, by decide⟩, false), (⟨22, by decide⟩, false), (⟨38, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c207, some c778, some c767, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c20, c207, c778, c767] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c767 := derived767 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c76, some c42, some c74, some c360, some c1320, some c32, some c1321, some c115, some c143, some c219, some c60, some c51, some c319, some c350, some c49, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c22, c76, c42, c74, c360, c1320, c32, c1321, c115, c143, c219, c60, c51, c319, c350, c49] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c1320 := derived1320 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c1321 := derived1321 a h
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1312, some c108, some c1077, some c1282, some c1315, some c1318, some c1322, some c1199, some c1319, some c4, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1312, c108, c1077, c1282, c1315, c1318, c1322, c1199, c1319, c4] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1312 := derived1312 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1315 := derived1315 a h
  have h5 : Entails.eval a c1318 := derived1318 a h
  have h6 : Entails.eval a c1322 := derived1322 a h
  have h7 : Entails.eval a c1199 := derived1199 a h
  have h8 : Entails.eval a c1319 := derived1319 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1077, some c108, some c1312, some c1323, some c107, some c1199, some c22, some c42, some c1320, some c1168, some c1037, some c20, some c33, some c356, some c223, some c44, some c61, some c52, some c63, some c344, some c319, some c143, some c5, some c1206, some c122, some c326, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1282, c1077, c108, c1312, c1323, c107, c1199, c22, c42, c1320, c1168, c1037, c20, c33, c356, c223, c44, c61, c52, c63, c344, c319, c143, c5, c1206, c122, c326] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1312 := derived1312 a h
  have h4 : Entails.eval a c1323 := derived1323 a h
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c1199 := derived1199 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1320 := derived1320 a h
  have h10 : Entails.eval a c1168 := derived1168 a h
  have h11 : Entails.eval a c1037 := derived1037 a h
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  have h20 : Entails.eval a c344 := h 343 (by decide)
  have h21 : Entails.eval a c319 := h 318 (by decide)
  have h22 : Entails.eval a c143 := h 142 (by decide)
  have h23 : Entails.eval a c5 := h 4 (by decide)
  have h24 : Entails.eval a c1206 := derived1206 a h
  have h25 : Entails.eval a c122 := h 121 (by decide)
  have h26 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c70, some c74, some c360, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c76, c70, c74, c360] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨39, by decide⟩, false), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c39, some c219, some c272, some c60, some c51, some c1095, some c319, some c350, some c49, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c19, c39, c219, c272, c60, c51, c1095, c319, c350, c49] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c1095 := derived1095 a h
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c20, some c1326, some c359, some c841, some c41, some c797, some c47, some c319, some c60, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c32, c20, c1326, c359, c841, c41, c797, c47, c319, c60] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c1326 := derived1326 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c797 := derived797 a h
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c32, some c1327, some c462, some c797, some c359, some c19, some c39, some c219, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c20, c32, c1327, c462, c797, c359, c19, c39, c219] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c1327 := derived1327 a h
  have h3 : Entails.eval a c462 := derived462 a h
  have h4 : Entails.eval a c797 := derived797 a h
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c602, some c48, some c928, some c257, some c98, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c19, c602, c48, c928, c257, c98] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c602 := derived602 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c928 := derived928 a h
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c40, some c928, some c345, some c98, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c48, c40, c928, c345, c98] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c928 := derived928 a h
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨28, by decide⟩, false), (⟨20, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c1095, some c220, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c41, c1095, c220] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c1095 := derived1095 a h
  have h2 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1325, some c1328, some c1329, some c1330, some c1331, some c359, some c360, some c72, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c1282, c1324, c1325, c1328, c1329, c1330, c1331, c359, c360, c72] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c1328 := derived1328 a h
  have h4 : Entails.eval a c1329 := derived1329 a h
  have h5 : Entails.eval a c1330 := derived1330 a h
  have h6 : Entails.eval a c1331 := derived1331 a h
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c360 := h 359 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c136, some c156, some c219, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c136, c156, c219] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c142, some c980, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c114, c142, c980] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c980 := derived980 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨35, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c207, some c167, some c1334, some c358, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c6, c207, c167, c1334, c358] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c1334 := derived1334 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1325, some c19, some c39, some c1335, some c116, some c136, some c892, some c1333, some c357, some c219, some c49, some c316, some c51, some c41, some c350, some c277, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1282, c1325, c19, c39, c1335, c116, c136, c892, c1333, c357, c219, c49, c316, c51, c41, c350, c277] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1325 := derived1325 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1335 := derived1335 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c892 := derived892 a h
  have h8 : Entails.eval a c1333 := derived1333 a h
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c350 := h 349 (by decide)
  have h16 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c360, some c792, some c280, some c232, some c6, some c685, some c165, some c358, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c359, c360, c792, c280, c232, c6, c685, c165, c358] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c685 := derived685 a h
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨39, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨35, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c1324, some c1282, some c272, some c218, some c36, some c127, some c136, some c58, some c331, some c207, some c854, some c179, some c336, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c201, c1324, c1282, c272, c218, c36, c127, c136, c58, c331, c207, c854, c179, c336] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c218 := h 217 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c331 := h 330 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c854 := derived854 a h
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨34, by decide⟩, true), (⟨21, by decide⟩, false), (⟨37, by decide⟩, true), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c30, some c797, some c1096, some c265, some c156, some c354, some c207, some c225, some c135, some c270, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c1282, c30, c797, c1096, c265, c156, c354, c207, c225, c135, c270] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c797 := derived797 a h
  have h3 : Entails.eval a c1096 := derived1096 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c225 := h 224 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨34, by decide⟩, true), (⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1325, some c1332, some c201, some c1336, some c1337, some c1095, some c41, some c1338, some c1339, some c127, some c136, some c331, some c207, some c123, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1282, c1324, c1325, c1332, c201, c1336, c1337, c1095, c41, c1338, c1339, c127, c136, c331, c207, c123] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c1337 := derived1337 a h
  have h7 : Entails.eval a c1095 := derived1095 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c1338 := derived1338 a h
  have h10 : Entails.eval a c1339 := derived1339 a h
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c331 := h 330 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c465, some c462, some c797, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c465, c462, c797] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c465 := derived465 a h
  have h1 : Entails.eval a c462 := derived462 a h
  have h2 : Entails.eval a c797 := derived797 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1332, some c201, some c1336, some c1282, some c1325, some c1337, some c41, some c1095, some c1341, some c1338, some c1340, some c30, some c358, some c357, some c120, some c1096, some c144, some c270, some c6, some c133, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c1324, c1332, c201, c1336, c1282, c1325, c1337, c41, c1095, c1341, c1338, c1340, c30, c358, c357, c120, c1096, c144, c270, c6, c133] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c1336 := derived1336 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c1337 := derived1337 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c1095 := derived1095 a h
  have h9 : Entails.eval a c1341 := derived1341 a h
  have h10 : Entails.eval a c1338 := derived1338 a h
  have h11 : Entails.eval a c1340 := derived1340 a h
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c1096 := derived1096 a h
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c6 := h 5 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c360, some c792, some c232, some c462, some c6, some c685, some c165, some c358, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c359, c360, c792, c232, c462, c6, c685, c165, c358] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c462 := derived462 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c685 := derived685 a h
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c1332, some c1282, some c1324, some c1325, some c1336, some c1342, some c1343, some c41, some c1095, some c1341, some c319, some c1338, some c47, some c58, some c30, some c347, some c854, some c317, some c51, some c844, some c313, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c201, c1332, c1282, c1324, c1325, c1336, c1342, c1343, c41, c1095, c1341, c319, c1338, c47, c58, c30, c347, c854, c317, c51, c844, c313] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1324 := derived1324 a h
  have h4 : Entails.eval a c1325 := derived1325 a h
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c1342 := derived1342 a h
  have h7 : Entails.eval a c1343 := derived1343 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c1095 := derived1095 a h
  have h10 : Entails.eval a c1341 := derived1341 a h
  have h11 : Entails.eval a c319 := h 318 (by decide)
  have h12 : Entails.eval a c1338 := derived1338 a h
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c347 := h 346 (by decide)
  have h17 : Entails.eval a c854 := derived854 a h
  have h18 : Entails.eval a c317 := h 316 (by decide)
  have h19 : Entails.eval a c51 := h 50 (by decide)
  have h20 : Entails.eval a c844 := derived844 a h
  have h21 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c1324, some c1282, some c19, some c602, some c39, some c1335, some c271, some c892, some c157, some c34, some c62, some c314, some c318, some c854, some c844, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c201, c1324, c1282, c19, c602, c39, c1335, c271, c892, c157, c34, c62, c314, c318, c854, c844] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c602 := derived602 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c1335 := derived1335 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c892 := derived892 a h
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c314 := h 313 (by decide)
  have h13 : Entails.eval a c318 := h 317 (by decide)
  have h14 : Entails.eval a c854 := derived854 a h
  have h15 : Entails.eval a c844 := derived844 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c360, some c792, some c280, some c465, some c6, some c685, some c165, some c358, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c359, c360, c792, c280, c465, c6, c685, c165, c358] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c465 := derived465 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c685 := derived685 a h
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1282, some c892, some c156, some c157, some c58, some c313, some c318, some c854, some c844, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c1324, c1282, c892, c156, c157, c58, c313, c318, c854, c844] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c892 := derived892 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c854 := derived854 a h
  have h9 : Entails.eval a c844 := derived844 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1282, some c1346, some c41, some c1095, some c271, some c30, some c269, some c1347, some c6, some c114, some c133, some c358, some c1096, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c1324, c1282, c1346, c41, c1095, c271, c30, c269, c1347, c6, c114, c133, c358, c1096] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1346 := derived1346 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c1095 := derived1095 a h
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c1347 := derived1347 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c1096 := derived1096 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1331, some c360, some c792, some c465, some c462, some c6, some c685, some c165, some c358, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c1348, c1331, c360, c792, c465, c462, c6, c685, c165, c358] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1331 := derived1331 a h
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c465 := derived465 a h
  have h5 : Entails.eval a c462 := derived462 a h
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c685 := derived685 a h
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1332, some c1282, some c1324, some c1325, some c201, some c1344, some c1345, some c1349, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c1332, c1282, c1324, c1325, c201, c1344, c1345, c1349] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c1332 := derived1332 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c1344 := derived1344 a h
  have h6 : Entails.eval a c1345 := derived1345 a h
  have h7 : Entails.eval a c1349 := derived1349 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c1290, some c1303, some c734, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c120, c1290, c1303, c734] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c1290 := derived1290 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c734 := derived734 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c673, some c137, some c225, some c1303, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c116, c673, c137, c225, c1303] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c673 := derived673 a h
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c1303 := derived1303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1282, some c19, some c39, some c1351, some c358, some c354, some c1352, some c6, some c114, some c142, some c213, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1324, c1282, c19, c39, c1351, c358, c354, c1352, c6, c114, c142, c213] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1351 := derived1351 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c1352 := derived1352 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1325, some c1350, some c1332, some c1353, some c667, some c354, some c358, some c1352, some c6, some c164, some c114, some c142, some c359, some c360, some c554, some c525, some c34, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c1282, c1324, c1325, c1350, c1332, c1353, c667, c354, c358, c1352, c6, c164, c114, c142, c359, c360, c554, c525, c34] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c1350 := derived1350 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1353 := derived1353 a h
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c1352 := derived1352 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c554 := derived554 a h
  have h17 : Entails.eval a c525 := derived525 a h
  have h18 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1303, some c270, some c225, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 57) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c1303, c270, c225] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c1303 := derived1303 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c1350, some c1332, some c1282, some c1324, some c1325, some c1353, some c667, some c358, some c354, some c1354, some c30, some c1355, some c139, some c128, some c137, some c135, some c84, some c80, some c6, some c1139, some c176, some c360, some c662, some c465, some c265, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 57) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c4, c1350, c1332, c1282, c1324, c1325, c1353, c667, c358, c354, c1354, c30, c1355, c139, c128, c137, c135, c84, c80, c6, c1139, c176, c360, c662, c465, c265] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c1350 := derived1350 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1324 := derived1324 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c1353 := derived1353 a h
  have h7 : Entails.eval a c667 := derived667 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c1354 := derived1354 a h
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c1355 := derived1355 a h
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c135 := h 134 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c6 := h 5 (by decide)
  have h20 : Entails.eval a c1139 := derived1139 a h
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c360 := h 359 (by decide)
  have h23 : Entails.eval a c662 := derived662 a h
  have h24 : Entails.eval a c465 := derived465 a h
  have h25 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c1351, some c34, some c139, some c358, some c354, some c1355, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 57) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c271, c1351, c34, c139, c358, c354, c1355] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c1351 := derived1351 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c1355 := derived1355 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1325, some c4, some c1350, some c1356, some c1357, some c30, some c19, some c269, some c667, some c358, some c354, some c225, some c1355, some c139, some c128, some c265, some c84, some c229, some c241, some c336, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 57) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c1282, c1324, c1325, c4, c1350, c1356, c1357, c30, c19, c269, c667, c358, c354, c225, c1355, c139, c128, c265, c84, c229, c241, c336] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c1350 := derived1350 a h
  have h5 : Entails.eval a c1356 := derived1356 a h
  have h6 : Entails.eval a c1357 := derived1357 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c269 := h 268 (by decide)
  have h10 : Entails.eval a c667 := derived667 a h
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c1355 := derived1355 a h
  have h15 : Entails.eval a c139 := h 138 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c265 := h 264 (by decide)
  have h18 : Entails.eval a c84 := h 83 (by decide)
  have h19 : Entails.eval a c229 := h 228 (by decide)
  have h20 : Entails.eval a c241 := h 240 (by decide)
  have h21 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨20, by decide⟩, true), (⟨40, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1333, some c892, some c316, some c62, some c63, some c844, some c314, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 57) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c1333, c892, c316, c62, c63, c844, c314] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c1333 := derived1333 a h
  have h1 : Entails.eval a c892 := derived892 a h
  have h2 : Entails.eval a c316 := h 315 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c844 := derived844 a h
  have h6 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨34, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c142, some c213, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 57) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c114, c142, c213] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨35, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1332, some c1324, some c19, some c39, some c1282, some c1325, some c1358, some c71, some c358, some c1360, some c6, some c1354, some c1359, some c203, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 57) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c1332, c1324, c19, c39, c1282, c1325, c1358, c71, c358, c1360, c6, c1354, c1359, c203] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c1332 := derived1332 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c1358 := derived1358 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c1360 := derived1360 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c1354 := derived1354 a h
  have h12 : Entails.eval a c1359 := derived1359 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1358, some c1282, some c1324, some c1325, some c19, some c1114, some c71, some c358, some c1361, some c268, some c271, some c225, some c35, some c1303, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 57) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c1358, c1282, c1324, c1325, c19, c1114, c71, c358, c1361, c268, c271, c225, c35, c1303] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c1358 := derived1358 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c1114 := derived1114 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c1361 := derived1361 a h
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c225 := h 224 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c1303 := derived1303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1362, some c1358, some c1282, some c1324, some c1325, some c1350, some c1354, some c667, some c30, some c31, some c358, some c354, some c1355, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 57) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1362, c1358, c1282, c1324, c1325, c1350, c1354, c667, c30, c31, c358, c354, c1355] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1358 := derived1358 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1324 := derived1324 a h
  have h4 : Entails.eval a c1325 := derived1325 a h
  have h5 : Entails.eval a c1350 := derived1350 a h
  have h6 : Entails.eval a c1354 := derived1354 a h
  have h7 : Entails.eval a c667 := derived667 a h
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c1355 := derived1355 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c792, some c136, some c1095, some c272, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 57) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c792, c136, c1095, c272] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c792 := derived792 a h
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c1095 := derived1095 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1282, some c114, some c142, some c165, some c1360, some c554, some c47, some c36, some c841, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 57) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c1324, c1282, c114, c142, c165, c1360, c554, c47, c36, c841] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c1360 := derived1360 a h
  have h6 : Entails.eval a c554 := derived554 a h
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1363, some c203, some c202, some c1362, some c1358, some c1332, some c1282, some c1324, some c1325, some c1364, some c6, some c1365, some c358, some c75, some c745, some c360, some c465, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 57) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c1363, c203, c202, c1362, c1358, c1332, c1282, c1324, c1325, c1364, c6, c1365, c358, c75, c745, c360, c465] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c1363 := derived1363 a h
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1362 := derived1362 a h
  have h4 : Entails.eval a c1358 := derived1358 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1324 := derived1324 a h
  have h8 : Entails.eval a c1325 := derived1325 a h
  have h9 : Entails.eval a c1364 := derived1364 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c1365 := derived1365 a h
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c745 := derived745 a h
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c465 := derived465 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨38, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c354, some c1355, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 57) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c358, c354, c1355] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c1355 := derived1355 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c62, some c64, some c320, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 57) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c58, c62, c64, c320] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1358, some c1282, some c1324, some c1368, some c1325, some c30, some c31, some c854, some c1367, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 57) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c1358, c1282, c1324, c1368, c1325, c30, c31, c854, c1367] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c1358 := derived1358 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1368 := derived1368 a h
  have h4 : Entails.eval a c1325 := derived1325 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c854 := derived854 a h
  have h8 : Entails.eval a c1367 := derived1367 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1368, some c1325, some c1358, some c1369, some c1366, some c271, some c34, some c35, some c854, some c1367, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 57) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c1282, c1324, c1368, c1325, c1358, c1369, c1366, c271, c34, c35, c854, c1367] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1368 := derived1368 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c1358 := derived1358 a h
  have h5 : Entails.eval a c1369 := derived1369 a h
  have h6 : Entails.eval a c1366 := derived1366 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c854 := derived854 a h
  have h11 : Entails.eval a c1367 := derived1367 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨27, by decide⟩, false), (⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c354, some c1360, some c162, some c8, some c204, some c137, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 57) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c358, c354, c1360, c162, c8, c204, c137] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c1360 := derived1360 a h
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨35, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1371, some c120, some c233, some c8, some c357, some c1360, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 57) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c1371, c120, c233, c8, c357, c1360] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c1371 := derived1371 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c1360 := derived1360 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c1372, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 57) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c39, c1372] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c1372 := derived1372 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1374 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c34, some c272, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 57) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c36, c34, c272] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c1368, some c1325, some c1373, some c1374, some c210, some c141, some c354, some c120, some c233, some c8, some c356, some c359, some c114, some c1149, some c1092, some c1159, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 57) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c1282, c631, c1303, c1368, c1325, c1373, c1374, c210, c141, c354, c120, c233, c8, c356, c359, c114, c1149, c1092, c1159] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c1368 := derived1368 a h
  have h4 : Entails.eval a c1325 := derived1325 a h
  have h5 : Entails.eval a c1373 := derived1373 a h
  have h6 : Entails.eval a c1374 := derived1374 a h
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c233 := h 232 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c1149 := derived1149 a h
  have h17 : Entails.eval a c1092 := derived1092 a h
  have h18 : Entails.eval a c1159 := derived1159 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c1368, some c1325, some c1375, some c30, some c19, some c210, some c141, some c354, some c120, some c233, some c8, some c356, some c359, some c114, some c1149, some c1092, some c1159, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 57) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c1282, c631, c1303, c1368, c1325, c1375, c30, c19, c210, c141, c354, c120, c233, c8, c356, c359, c114, c1149, c1092, c1159] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c1368 := derived1368 a h
  have h4 : Entails.eval a c1325 := derived1325 a h
  have h5 : Entails.eval a c1375 := derived1375 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c233 := h 232 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c1149 := derived1149 a h
  have h18 : Entails.eval a c1092 := derived1092 a h
  have h19 : Entails.eval a c1159 := derived1159 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1303, some c1368, some c1325, some c31, some c24, some c1374, some c354, some c210, some c141, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 57) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c631, c1303, c1368, c1325, c31, c24, c1374, c354, c210, c141] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c1368 := derived1368 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1374 := derived1374 a h
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨8, by decide⟩, false), (⟨9, by decide⟩, true), (⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c1374, some c271, some c221, some c210, some c21, some c151, some c141, some c353, some c354, some c23, some c43, some c120, some c219, some c8, some c150, some c638, some c207, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 57) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c1282, c631, c1303, c1374, c271, c221, c210, c21, c151, c141, c353, c354, c23, c43, c120, c219, c8, c150, c638, c207] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c1374 := derived1374 a h
  have h4 : Entails.eval a c271 := h 270 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c219 := h 218 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c150 := h 149 (by decide)
  have h18 : Entails.eval a c638 := derived638 a h
  have h19 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1282, some c1325, some c1368, some c1370, some c631, some c1377, some c1376, some c1378, some c30, some c19, some c269, some c221, some c210, some c1330, some c151, some c141, some c6, some c354, some c114, some c149, some c357, some c318, some c281, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 57) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c1324, c1282, c1325, c1368, c1370, c631, c1377, c1376, c1378, c30, c19, c269, c221, c210, c1330, c151, c141, c6, c354, c114, c149, c357, c318, c281] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c1368 := derived1368 a h
  have h4 : Entails.eval a c1370 := derived1370 a h
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c1377 := derived1377 a h
  have h7 : Entails.eval a c1376 := derived1376 a h
  have h8 : Entails.eval a c1378 := derived1378 a h
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c221 := h 220 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c1330 := derived1330 a h
  have h15 : Entails.eval a c151 := h 150 (by decide)
  have h16 : Entails.eval a c141 := h 140 (by decide)
  have h17 : Entails.eval a c6 := h 5 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c114 := h 113 (by decide)
  have h20 : Entails.eval a c149 := h 148 (by decide)
  have h21 : Entails.eval a c357 := h 356 (by decide)
  have h22 : Entails.eval a c318 := h 317 (by decide)
  have h23 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨30, by decide⟩, false), (⟨35, by decide⟩, false), (⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c145, some c218, some c272, some c47, some c839, some c32, some c258, some c734, some c1303, some c128, some c137, some c336, some c1139, some c244, some c341, some c328, some c88, some c364, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 57) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c360, c145, c218, c272, c47, c839, c32, c258, c734, c1303, c128, c137, c336, c1139, c244, c341, c328, c88, c364] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c218 := h 217 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c839 := derived839 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c734 := derived734 a h
  have h9 : Entails.eval a c1303 := derived1303 a h
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c1139 := derived1139 a h
  have h14 : Entails.eval a c244 := h 243 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c328 := h 327 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c1282, some c20, some c116, some c227, some c205, some c1303, some c265, some c128, some c336, some c84, some c244, some c176, some c88, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 57) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c355, c1282, c20, c116, c227, c205, c1303, c265, c128, c336, c84, c244, c176, c88] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c227 := h 226 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c128 := h 127 (by decide)
  have h9 : Entails.eval a c336 := h 335 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1355, some c164, some c137, some c205, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 57) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c1355, c164, c137, c205] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c1355 := derived1355 a h
  have h1 : Entails.eval a c164 := h 163 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1379, some c1, some c1324, some c1282, some c22, some c76, some c70, some c42, some c854, some c360, some c355, some c170, some c1095, some c202, some c1380, some c1382, some c356, some c227, some c1381, some c1303, some c31, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 57) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1379, c1, c1324, c1282, c22, c76, c70, c42, c854, c360, c355, c170, c1095, c202, c1380, c1382, c356, c227, c1381, c1303, c31] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c854 := derived854 a h
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c1095 := derived1095 a h
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c1380 := derived1380 a h
  have h15 : Entails.eval a c1382 := derived1382 a h
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c227 := h 226 (by decide)
  have h18 : Entails.eval a c1381 := derived1381 a h
  have h19 : Entails.eval a c1303 := derived1303 a h
  have h20 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1383

end CochromaticTwenty.Certificates.B16_4_2
