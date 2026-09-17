import MerLeanExperiment.Certificates.B16_2_0.Steps0800_0899

/-! Generated from the actual pinned b16_2_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1289 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨15, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1170, some c1172, some c294, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 57) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c1170, c1172, c294] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c1170 := derived1170 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1289, some c47, some c141, some c131, some c294, some c64, some c130, some c1175, some c335, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 57) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c1289, c47, c141, c131, c294, c64, c130, c1175, c335] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c1289 := derived1289 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c1175 := derived1175 a h
  have h8 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1291 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1278, some c386, some c97, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 57) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c1226, c1278, c386, c97] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1278 := derived1278 a h
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1290, some c180, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 57) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c1290, c180] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c1290 := derived1290 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1293 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1169, some c1171, some c64, some c45, some c131, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 57) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c1169, c1171, c64, c45, c131] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c1169 := derived1169 a h
  have h1 : Entails.eval a c1171 := derived1171 a h
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1293, some c47, some c131, some c64, some c62, some c1174, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 57) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c1293, c47, c131, c64, c62, c1174] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c1293 := derived1293 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c1174 := derived1174 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c1163, some c109, some c9, some c1, some c1292, some c197, some c1294, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 57) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c104, c1163, c109, c9, c1, c1292, c197, c1294] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c1163 := derived1163 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1292 := derived1292 a h
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c1294 := derived1294 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c120, some c33, some c28, some c256, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 57) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c1226, c120, c33, c28, c256] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1169, some c1171, some c64, some c45, some c199, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 57) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c1169, c1171, c64, c45, c199] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c1169 := derived1169 a h
  have h1 : Entails.eval a c1171 := derived1171 a h
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1298 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1297, some c47, some c199, some c64, some c62, some c1174, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 57) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c1297, c47, c199, c64, c62, c1174] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c1297 := derived1297 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c1174 := derived1174 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c1163, some c109, some c9, some c194, some c1296, some c1298, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 57) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c104, c1163, c109, c9, c194, c1296, c1298] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c1163 := derived1163 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1296 := derived1296 a h
  have h6 : Entails.eval a c1298 := derived1298 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c104, some c1, some c9, some c1163, some c1299, some c1294, some c1295, some c197, some c1291, some c1290, some c1181, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 57) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c109, c104, c1, c9, c1163, c1299, c1294, c1295, c197, c1291, c1290, c1181] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1163 := derived1163 a h
  have h5 : Entails.eval a c1299 := derived1299 a h
  have h6 : Entails.eval a c1294 := derived1294 a h
  have h7 : Entails.eval a c1295 := derived1295 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c1291 := derived1291 a h
  have h10 : Entails.eval a c1290 := derived1290 a h
  have h11 : Entails.eval a c1181 := derived1181 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c104, some c109, some c1300, some c1182, some c1282, some c1286, some c1288, some c3, some c14, some c1091, some c384, some c78, some c101, some c1058, some c1176, some c171, some c73, some c20, some c1166, some c115, some c240, some c37, some c22, some c253, some c377, some c236, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 57) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c1226, c104, c109, c1300, c1182, c1282, c1286, c1288, c3, c14, c1091, c384, c78, c101, c1058, c1176, c171, c73, c20, c1166, c115, c240, c37, c22, c253, c377, c236] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c1300 := derived1300 a h
  have h4 : Entails.eval a c1182 := derived1182 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1286 := derived1286 a h
  have h7 : Entails.eval a c1288 := derived1288 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c1091 := derived1091 a h
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c1058 := derived1058 a h
  have h15 : Entails.eval a c1176 := derived1176 a h
  have h16 : Entails.eval a c171 := h 170 (by decide)
  have h17 : Entails.eval a c73 := h 72 (by decide)
  have h18 : Entails.eval a c20 := h 19 (by decide)
  have h19 : Entails.eval a c1166 := derived1166 a h
  have h20 : Entails.eval a c115 := h 114 (by decide)
  have h21 : Entails.eval a c240 := h 239 (by decide)
  have h22 : Entails.eval a c37 := h 36 (by decide)
  have h23 : Entails.eval a c22 := h 21 (by decide)
  have h24 : Entails.eval a c253 := h 252 (by decide)
  have h25 : Entails.eval a c377 := h 376 (by decide)
  have h26 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1182, some c14, some c162, some c171, some c81, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 57) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c1226, c1182, c14, c162, c171, c81] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1182 := derived1182 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1303 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1182, some c13, some c189, some c1183, some c1302, some c76, some c875, some c1283, some c180, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 57) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c1226, c1182, c13, c189, c1183, c1302, c76, c875, c1283, c180] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1182 := derived1182 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1183 := derived1183 a h
  have h5 : Entails.eval a c1302 := derived1302 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c875 := derived875 a h
  have h8 : Entails.eval a c1283 := derived1283 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1301, some c1182, some c13, some c3, some c1303, some c110, some c1162, some c1091, some c384, some c927, some c928, some c162, some c22, some c73, some c20, some c240, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 57) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c1226, c1301, c1182, c13, c3, c1303, c110, c1162, c1091, c384, c927, c928, c162, c22, c73, c20, c240] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1182 := derived1182 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c1303 := derived1303 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1162 := derived1162 a h
  have h8 : Entails.eval a c1091 := derived1091 a h
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c927 := derived927 a h
  have h11 : Entails.eval a c928 := derived928 a h
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c14, some c1275, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 57) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1226, c14, c1275] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c1275 := derived1275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c85, some c89, some c377, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 57) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c1226, c85, c89, c377] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c15, some c154, some c155, some c69, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 57) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c1226, c15, c154, c155, c69] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1301, some c1182, some c1183, some c3, some c13, some c15, some c189, some c1304, some c962, some c1305, some c110, some c1162, some c1091, some c384, some c99, some c78, some c180, some c382, some c388, some c1176, some c358, some c1306, some c171, some c1307, some c341, some c1169, some c300, some c143, some c144, some c52, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 57) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c1226, c1301, c1182, c1183, c3, c13, c15, c189, c1304, c962, c1305, c110, c1162, c1091, c384, c99, c78, c180, c382, c388, c1176, c358, c1306, c171, c1307, c341, c1169, c300, c143, c144, c52] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1182 := derived1182 a h
  have h3 : Entails.eval a c1183 := derived1183 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c1304 := derived1304 a h
  have h9 : Entails.eval a c962 := derived962 a h
  have h10 : Entails.eval a c1305 := derived1305 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c1162 := derived1162 a h
  have h13 : Entails.eval a c1091 := derived1091 a h
  have h14 : Entails.eval a c384 := h 383 (by decide)
  have h15 : Entails.eval a c99 := h 98 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c382 := h 381 (by decide)
  have h19 : Entails.eval a c388 := h 387 (by decide)
  have h20 : Entails.eval a c1176 := derived1176 a h
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c1306 := derived1306 a h
  have h23 : Entails.eval a c171 := h 170 (by decide)
  have h24 : Entails.eval a c1307 := derived1307 a h
  have h25 : Entails.eval a c341 := h 340 (by decide)
  have h26 : Entails.eval a c1169 := derived1169 a h
  have h27 : Entails.eval a c300 := h 299 (by decide)
  have h28 : Entails.eval a c143 := h 142 (by decide)
  have h29 : Entails.eval a c144 := h 143 (by decide)
  have h30 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1308, some c1163, some c110, some c9, some c1, some c197, some c194, some c1290, some c1292, some c1181, some c1291, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 57) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c1308, c1163, c110, c9, c1, c197, c194, c1290, c1292, c1181, c1291] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c1308 := derived1308 a h
  have h1 : Entails.eval a c1163 := derived1163 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c1290 := derived1290 a h
  have h8 : Entails.eval a c1292 := derived1292 a h
  have h9 : Entails.eval a c1181 := derived1181 a h
  have h10 : Entails.eval a c1291 := derived1291 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1170, some c1171, some c292, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 57) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c1170, c1171, c292] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c1170 := derived1170 a h
  have h1 : Entails.eval a c1171 := derived1171 a h
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1311 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1173, some c1174, some c333, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1311 : lratChecker f1311 p1311 = .success := by decide +kernel
theorem unsat1311 : Unsatisfiable (PosFin 57) f1311 := by
  apply lratCheckerSound f1311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1311
  · intro a ha; simp [p1311] at ha; subst a; trivial
  · exact checked1311
theorem derived1311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1311 := by
  apply localUnsat_implies_entails f1311 [c1173, c1174, c333] c1311 unsat1311 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1174 := derived1174 a h
  have h2 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1312 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1308, some c1301, some c1, some c1163, some c110, some c9, some c1275, some c1309, some c4, some c1310, some c55, some c47, some c1311, some c72, some c64, some c268, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1312 : lratChecker f1312 p1312 = .success := by decide +kernel
theorem unsat1312 : Unsatisfiable (PosFin 57) f1312 := by
  apply lratCheckerSound f1312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1312
  · intro a ha; simp [p1312] at ha; subst a; trivial
  · exact checked1312
theorem derived1312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1312 := by
  apply localUnsat_implies_entails f1312 [c1308, c1301, c1, c1163, c110, c9, c1275, c1309, c4, c1310, c55, c47, c1311, c72, c64, c268] c1312 unsat1312 (by rfl) a
  have h0 : Entails.eval a c1308 := derived1308 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1163 := derived1163 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1275 := derived1275 a h
  have h7 : Entails.eval a c1309 := derived1309 a h
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c1310 := derived1310 a h
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c1311 := derived1311 a h
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1313 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1308, some c1312, some c1262, some c1301, some c1276, some c1164, some c194, some c197, some c1272, some c1153, some c180, some c1278, some c380, some c96, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1313 : lratChecker f1313 p1313 = .success := by decide +kernel
theorem unsat1313 : Unsatisfiable (PosFin 57) f1313 := by
  apply lratCheckerSound f1313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1313
  · intro a ha; simp [p1313] at ha; subst a; trivial
  · exact checked1313
theorem derived1313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1313 := by
  apply localUnsat_implies_entails f1313 [c1226, c1308, c1312, c1262, c1301, c1276, c1164, c194, c197, c1272, c1153, c180, c1278, c380, c96] c1313 unsat1313 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1308 := derived1308 a h
  have h2 : Entails.eval a c1312 := derived1312 a h
  have h3 : Entails.eval a c1262 := derived1262 a h
  have h4 : Entails.eval a c1301 := derived1301 a h
  have h5 : Entails.eval a c1276 := derived1276 a h
  have h6 : Entails.eval a c1164 := derived1164 a h
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c1272 := derived1272 a h
  have h10 : Entails.eval a c1153 := derived1153 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c1278 := derived1278 a h
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1314 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1308, some c1312, some c1276, some c1262, some c1301, some c1164, some c197, some c1165, some c1170, some c1172, some c43, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 57) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c1308, c1312, c1276, c1262, c1301, c1164, c197, c1165, c1170, c1172, c43] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c1308 := derived1308 a h
  have h1 : Entails.eval a c1312 := derived1312 a h
  have h2 : Entails.eval a c1276 := derived1276 a h
  have h3 : Entails.eval a c1262 := derived1262 a h
  have h4 : Entails.eval a c1301 := derived1301 a h
  have h5 : Entails.eval a c1164 := derived1164 a h
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c1165 := derived1165 a h
  have h8 : Entails.eval a c1170 := derived1170 a h
  have h9 : Entails.eval a c1172 := derived1172 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨55, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1308, some c1312, some c1272, some c1081, some c78, some c1301, some c99, some c388, some c1313, some c1262, some c1276, some c1164, some c1306, some c171, some c358, some c371, some c22, some c370, some c373, some c1162, some c75, some c249, some c36, some c251, some c231, some c256, some c124, some c197, some c1165, some c1275, some c52, some c43, some c206, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 57) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c1226, c1308, c1312, c1272, c1081, c78, c1301, c99, c388, c1313, c1262, c1276, c1164, c1306, c171, c358, c371, c22, c370, c373, c1162, c75, c249, c36, c251, c231, c256, c124, c197, c1165, c1275, c52, c43, c206] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1308 := derived1308 a h
  have h2 : Entails.eval a c1312 := derived1312 a h
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c1081 := derived1081 a h
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c1301 := derived1301 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c1313 := derived1313 a h
  have h10 : Entails.eval a c1262 := derived1262 a h
  have h11 : Entails.eval a c1276 := derived1276 a h
  have h12 : Entails.eval a c1164 := derived1164 a h
  have h13 : Entails.eval a c1306 := derived1306 a h
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c358 := h 357 (by decide)
  have h16 : Entails.eval a c371 := h 370 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c370 := h 369 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  have h20 : Entails.eval a c1162 := derived1162 a h
  have h21 : Entails.eval a c75 := h 74 (by decide)
  have h22 : Entails.eval a c249 := h 248 (by decide)
  have h23 : Entails.eval a c36 := h 35 (by decide)
  have h24 : Entails.eval a c251 := h 250 (by decide)
  have h25 : Entails.eval a c231 := h 230 (by decide)
  have h26 : Entails.eval a c256 := h 255 (by decide)
  have h27 : Entails.eval a c124 := h 123 (by decide)
  have h28 : Entails.eval a c197 := h 196 (by decide)
  have h29 : Entails.eval a c1165 := derived1165 a h
  have h30 : Entails.eval a c1275 := derived1275 a h
  have h31 : Entails.eval a c52 := h 51 (by decide)
  have h32 : Entails.eval a c43 := h 42 (by decide)
  have h33 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1313, some c1308, some c1312, some c1276, some c1262, some c1301, some c1164, some c197, some c1165, some c194, some c1162, some c1272, some c1275, some c1081, some c99, some c78, some c388, some c1306, some c171, some c358, some c371, some c75, some c22, some c249, some c36, some c124, some c1315, some c136, some c141, some c69, some c46, some c202, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 57) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c1226, c1313, c1308, c1312, c1276, c1262, c1301, c1164, c197, c1165, c194, c1162, c1272, c1275, c1081, c99, c78, c388, c1306, c171, c358, c371, c75, c22, c249, c36, c124, c1315, c136, c141, c69, c46, c202] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1313 := derived1313 a h
  have h2 : Entails.eval a c1308 := derived1308 a h
  have h3 : Entails.eval a c1312 := derived1312 a h
  have h4 : Entails.eval a c1276 := derived1276 a h
  have h5 : Entails.eval a c1262 := derived1262 a h
  have h6 : Entails.eval a c1301 := derived1301 a h
  have h7 : Entails.eval a c1164 := derived1164 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c1165 := derived1165 a h
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c1162 := derived1162 a h
  have h12 : Entails.eval a c1272 := derived1272 a h
  have h13 : Entails.eval a c1275 := derived1275 a h
  have h14 : Entails.eval a c1081 := derived1081 a h
  have h15 : Entails.eval a c99 := h 98 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c388 := h 387 (by decide)
  have h18 : Entails.eval a c1306 := derived1306 a h
  have h19 : Entails.eval a c171 := h 170 (by decide)
  have h20 : Entails.eval a c358 := h 357 (by decide)
  have h21 : Entails.eval a c371 := h 370 (by decide)
  have h22 : Entails.eval a c75 := h 74 (by decide)
  have h23 : Entails.eval a c22 := h 21 (by decide)
  have h24 : Entails.eval a c249 := h 248 (by decide)
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c124 := h 123 (by decide)
  have h27 : Entails.eval a c1315 := derived1315 a h
  have h28 : Entails.eval a c136 := h 135 (by decide)
  have h29 : Entails.eval a c141 := h 140 (by decide)
  have h30 : Entails.eval a c69 := h 68 (by decide)
  have h31 : Entails.eval a c46 := h 45 (by decide)
  have h32 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1301, some c1308, some c1312, some c1262, some c1276, some c1162, some c1164, some c197, some c194, some c1165, some c1314, some c1316, some c180, some c298, some c141, some c131, some c43, some c56, some c974, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 57) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c1226, c1301, c1308, c1312, c1262, c1276, c1162, c1164, c197, c194, c1165, c1314, c1316, c180, c298, c141, c131, c43, c56, c974] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1308 := derived1308 a h
  have h3 : Entails.eval a c1312 := derived1312 a h
  have h4 : Entails.eval a c1262 := derived1262 a h
  have h5 : Entails.eval a c1276 := derived1276 a h
  have h6 : Entails.eval a c1162 := derived1162 a h
  have h7 : Entails.eval a c1164 := derived1164 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c1165 := derived1165 a h
  have h11 : Entails.eval a c1314 := derived1314 a h
  have h12 : Entails.eval a c1316 := derived1316 a h
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c298 := h 297 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c131 := h 130 (by decide)
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c56 := h 55 (by decide)
  have h19 : Entails.eval a c974 := derived974 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1226, some c1262, some c1272, some c1280, some c106, some c3, some c75, some c98, some c1177, some c1081, some c78, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 57) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c1317, c1226, c1262, c1272, c1280, c106, c3, c75, c98, c1177, c1081, c78] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c1262 := derived1262 a h
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c1280 := derived1280 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1177 := derived1177 a h
  have h10 : Entails.eval a c1081 := derived1081 a h
  have h11 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1262, some c1272, some c1280, some c106, some c1318, some c1278, some c94, some c95, some c1081, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c1317, c1262, c1272, c1280, c106, c1318, c1278, c94, c95, c1081] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1262 := derived1262 a h
  have h2 : Entails.eval a c1272 := derived1272 a h
  have h3 : Entails.eval a c1280 := derived1280 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1318 := derived1318 a h
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c1081 := derived1081 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1226, some c1319, some c1, some c74, some c1240, some c85, some c76, some c23, some c369, some c241, some c20, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c1317, c1226, c1319, c1, c74, c1240, c85, c76, c23, c369, c241, c20] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c1319 := derived1319 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c1240 := derived1240 a h
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1319, some c1, some c1278, some c380, some c96, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c1226, c1319, c1, c1278, c380, c96] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1319 := derived1319 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1278 := derived1278 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1226, some c1319, some c1, some c1321, some c2, some c74, some c1320, some c13, some c165, some c75, some c22, some c85, some c240, some c370, some c20, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c1317, c1226, c1319, c1, c1321, c2, c74, c1320, c13, c165, c75, c22, c85, c240, c370, c20] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c1319 := derived1319 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1321 := derived1321 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c1320 := derived1320 a h
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1317, some c1322, some c1319, some c1, some c2, some c74, some c1240, some c194, some c9, some c112, some c837, some c1035, some c1081, some c382, some c365, some c1178, some c373, some c1232, some c520, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1226, c1317, c1322, c1319, c1, c2, c74, c1240, c194, c9, c112, c837, c1035, c1081, c382, c365, c1178, c373, c1232, c520] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c1322 := derived1322 a h
  have h3 : Entails.eval a c1319 := derived1319 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c1240 := derived1240 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c837 := derived837 a h
  have h12 : Entails.eval a c1035 := derived1035 a h
  have h13 : Entails.eval a c1081 := derived1081 a h
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c365 := h 364 (by decide)
  have h16 : Entails.eval a c1178 := derived1178 a h
  have h17 : Entails.eval a c373 := h 372 (by decide)
  have h18 : Entails.eval a c1232 := derived1232 a h
  have h19 : Entails.eval a c520 := derived520 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1226, some c1323, some c1278, some c3, some c75, some c1177, some c1319, some c1, some c380, some c98, some c12, some c1081, some c365, some c172, some c84, some c1035, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1317, c1226, c1323, c1278, c3, c75, c1177, c1319, c1, c380, c98, c12, c1081, c365, c172, c84, c1035] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c1323 := derived1323 a h
  have h3 : Entails.eval a c1278 := derived1278 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c1177 := derived1177 a h
  have h7 : Entails.eval a c1319 := derived1319 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c1081 := derived1081 a h
  have h13 : Entails.eval a c365 := h 364 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c1035 := derived1035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1323, some c1322, some c1319, some c1, some c1324, some c112, some c9, some c1291, some c197, some c1181, some c527, some c523, some c130, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c1323, c1322, c1319, c1, c1324, c112, c9, c1291, c197, c1181, c527, c523, c130] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c1323 := derived1323 a h
  have h1 : Entails.eval a c1322 := derived1322 a h
  have h2 : Entails.eval a c1319 := derived1319 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1324 := derived1324 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c1291 := derived1291 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c1181 := derived1181 a h
  have h10 : Entails.eval a c527 := derived527 a h
  have h11 : Entails.eval a c523 := derived523 a h
  have h12 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1317, some c1322, some c1319, some c1, some c1323, some c1278, some c380, some c3, some c75, some c1325, some c194, some c165, some c9, some c21, some c112, some c239, some c98, some c84, some c20, some c1081, some c372, some c945, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c1226, c1317, c1322, c1319, c1, c1323, c1278, c380, c3, c75, c1325, c194, c165, c9, c21, c112, c239, c98, c84, c20, c1081, c372, c945] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c1322 := derived1322 a h
  have h3 : Entails.eval a c1319 := derived1319 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1323 := derived1323 a h
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c1325 := derived1325 a h
  have h11 : Entails.eval a c194 := h 193 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c98 := h 97 (by decide)
  have h18 : Entails.eval a c84 := h 83 (by decide)
  have h19 : Entails.eval a c20 := h 19 (by decide)
  have h20 : Entails.eval a c1081 := derived1081 a h
  have h21 : Entails.eval a c372 := h 371 (by decide)
  have h22 : Entails.eval a c945 := derived945 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨47, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c370, some c373, some c365, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c370, c373, c365] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c370 := h 369 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1226, some c74, some c1322, some c1319, some c1, some c112, some c837, some c1035, some c1081, some c382, some c1327, some c20, some c520, some c31, some c34, some c256, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c1317, c1226, c74, c1322, c1319, c1, c112, c837, c1035, c1081, c382, c1327, c20, c520, c31, c34, c256] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c1322 := derived1322 a h
  have h4 : Entails.eval a c1319 := derived1319 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c837 := derived837 a h
  have h8 : Entails.eval a c1035 := derived1035 a h
  have h9 : Entails.eval a c1081 := derived1081 a h
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c1327 := derived1327 a h
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c520 := derived520 a h
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1317, some c1226, some c1319, some c2, some c74, some c1328, some c9, some c167, some c86, some c81, some c369, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c1317, c1226, c1319, c2, c74, c1328, c9, c167, c86, c81, c369] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c1317 := derived1317 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c1319 := derived1319 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c1328 := derived1328 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1226, some c1317, some c1, some c1322, some c1326, some c1329, some c1278, some c380, some c3, some c75, some c1180, some c1177, some c1291, some c386, some c112, some c98, some c1081, some c561, some c84, some c1035, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c1226, c1317, c1, c1322, c1326, c1329, c1278, c380, c3, c75, c1180, c1177, c1291, c386, c112, c98, c1081, c561, c84, c1035] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c1226 := derived1226 a h
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1322 := derived1322 a h
  have h4 : Entails.eval a c1326 := derived1326 a h
  have h5 : Entails.eval a c1329 := derived1329 a h
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c1180 := derived1180 a h
  have h11 : Entails.eval a c1177 := derived1177 a h
  have h12 : Entails.eval a c1291 := derived1291 a h
  have h13 : Entails.eval a c386 := h 385 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c1081 := derived1081 a h
  have h17 : Entails.eval a c561 := derived561 a h
  have h18 : Entails.eval a c84 := h 83 (by decide)
  have h19 : Entails.eval a c1035 := derived1035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1319, some c1330, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c1319, c1330] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c1319 := derived1319 a h
  have h1 : Entails.eval a c1330 := derived1330 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1331, some c1182, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c1331, c1182] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c1182 := derived1182 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1331, some c1183, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c1331, c1183] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c1183 := derived1183 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1332, some c1226, some c3, some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c1332, c1226, c3] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c1332 := derived1332 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1333, some c1332, some c1226, some c15, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c1333, c1332, c1226, c15] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c1333 := derived1333 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1226 := derived1226 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1335, some c1332, some c1333, some c1331, some c1226, some c1334, some c1317, some c106, some c13, some c189, some c2, some c379, some c962, some c99, some c78, some c963, some c385, some c1176, some c377, some c358, some c22, some c376, some c244, some c21, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1335, c1332, c1333, c1331, c1226, c1334, c1317, c106, c13, c189, c2, c379, c962, c99, c78, c963, c385, c1176, c377, c358, c22, c376, c244, c21] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1335 := derived1335 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1333 := derived1333 a h
  have h3 : Entails.eval a c1331 := derived1331 a h
  have h4 : Entails.eval a c1226 := derived1226 a h
  have h5 : Entails.eval a c1334 := derived1334 a h
  have h6 : Entails.eval a c1317 := derived1317 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c962 := derived962 a h
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c963 := derived963 a h
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c1176 := derived1176 a h
  have h18 : Entails.eval a c377 := h 376 (by decide)
  have h19 : Entails.eval a c358 := h 357 (by decide)
  have h20 : Entails.eval a c22 := h 21 (by decide)
  have h21 : Entails.eval a c376 := h 375 (by decide)
  have h22 : Entails.eval a c244 := h 243 (by decide)
  have h23 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1333, some c1335, some c1332, some c1226, some c1331, some c106, some c13, some c962, some c1176, some c162, some c88, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c1333, c1335, c1332, c1226, c1331, c106, c13, c962, c1176, c162, c88] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c1333 := derived1333 a h
  have h1 : Entails.eval a c1335 := derived1335 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1226 := derived1226 a h
  have h4 : Entails.eval a c1331 := derived1331 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c962 := derived962 a h
  have h8 : Entails.eval a c1176 := derived1176 a h
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1333, some c1335, some c1332, some c1331, some c1317, some c1334, some c1226, some c106, some c13, some c189, some c2, some c379, some c384, some c1337, some c359, some c962, some c21, some c83, some c244, some c377, some c22, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c1333, c1335, c1332, c1331, c1317, c1334, c1226, c106, c13, c189, c2, c379, c384, c1337, c359, c962, c21, c83, c244, c377, c22] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c1333 := derived1333 a h
  have h1 : Entails.eval a c1335 := derived1335 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1331 := derived1331 a h
  have h4 : Entails.eval a c1317 := derived1317 a h
  have h5 : Entails.eval a c1334 := derived1334 a h
  have h6 : Entails.eval a c1226 := derived1226 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c384 := h 383 (by decide)
  have h13 : Entails.eval a c1337 := derived1337 a h
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c962 := derived962 a h
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c83 := h 82 (by decide)
  have h18 : Entails.eval a c244 := h 243 (by decide)
  have h19 : Entails.eval a c377 := h 376 (by decide)
  have h20 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1333, some c1335, some c1332, some c1331, some c1226, some c1334, some c1317, some c962, some c106, some c13, some c189, some c2, some c384, some c379, some c1336, some c1337, some c359, some c1338, some c374, some c22, some c248, some c244, some c30, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c1333, c1335, c1332, c1331, c1226, c1334, c1317, c962, c106, c13, c189, c2, c384, c379, c1336, c1337, c359, c1338, c374, c22, c248, c244, c30] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c1333 := derived1333 a h
  have h1 : Entails.eval a c1335 := derived1335 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1331 := derived1331 a h
  have h4 : Entails.eval a c1226 := derived1226 a h
  have h5 : Entails.eval a c1334 := derived1334 a h
  have h6 : Entails.eval a c1317 := derived1317 a h
  have h7 : Entails.eval a c962 := derived962 a h
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c384 := h 383 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c1336 := derived1336 a h
  have h15 : Entails.eval a c1337 := derived1337 a h
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c1338 := derived1338 a h
  have h18 : Entails.eval a c374 := h 373 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c248 := h 247 (by decide)
  have h21 : Entails.eval a c244 := h 243 (by decide)
  have h22 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1332, some c1334, some c1339, some c1331, some c1226, some c1317, some c13, some c189, some c2, some c379, some c73, some c162, some c85, some c76, some c23, some c369, some c245, some c21, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1332, c1334, c1339, c1331, c1226, c1317, c13, c189, c2, c379, c73, c162, c85, c76, c23, c369, c245, c21] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1332 := derived1332 a h
  have h1 : Entails.eval a c1334 := derived1334 a h
  have h2 : Entails.eval a c1339 := derived1339 a h
  have h3 : Entails.eval a c1331 := derived1331 a h
  have h4 : Entails.eval a c1226 := derived1226 a h
  have h5 : Entails.eval a c1317 := derived1317 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1340, some c1335, some c112, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c1340, c1335, c112] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1335 := derived1335 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1341, some c1331, some c1339, some c1282, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c1341, c1331, c1339, c1282] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c1341 := derived1341 a h
  have h1 : Entails.eval a c1331 := derived1331 a h
  have h2 : Entails.eval a c1339 := derived1339 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1342, some c1331, some c189, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c1342, c1331, c189] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c1342 := derived1342 a h
  have h1 : Entails.eval a c1331 := derived1331 a h
  have h2 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1343, some c1317, some c2, some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1343, c1317, c2] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1343 := derived1343 a h
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1344, some c1334, some c384, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c1344, c1334, c384] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c1344 := derived1344 a h
  have h1 : Entails.eval a c1334 := derived1334 a h
  have h2 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1344, some c1334, some c379, some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c1344, c1334, c379] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c1344 := derived1344 a h
  have h1 : Entails.eval a c1334 := derived1334 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1344, some c1341, some c1339, some c875, some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c1344, c1341, c1339, c875] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c1344 := derived1344 a h
  have h1 : Entails.eval a c1341 := derived1341 a h
  have h2 : Entails.eval a c1339 := derived1339 a h
  have h3 : Entails.eval a c875 := derived875 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1346, some c1339, some c73, some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c1346, c1339, c73] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c1346 := derived1346 a h
  have h1 : Entails.eval a c1339 := derived1339 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1346, some c1341, some c1339, some c92, some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c1346, c1341, c1339, c92] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c1346 := derived1346 a h
  have h1 : Entails.eval a c1341 := derived1341 a h
  have h2 : Entails.eval a c1339 := derived1339 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1347, some c1226, some c1345, some c1341, some c909, some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c1348, c1347, c1226, c1345, c1341, c909] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1347 := derived1347 a h
  have h2 : Entails.eval a c1226 := derived1226 a h
  have h3 : Entails.eval a c1345 := derived1345 a h
  have h4 : Entails.eval a c1341 := derived1341 a h
  have h5 : Entails.eval a c909 := derived909 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1350, some c1317, some c21, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1350, c1317, c21] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1350 := derived1350 a h
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1351, some c1344, some c1334, some c244, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c1351, c1344, c1334, c244] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1344 := derived1344 a h
  have h2 : Entails.eval a c1334 := derived1334 a h
  have h3 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1351, some c1344, some c1349, some c246, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1351, c1344, c1349, c246] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1344 := derived1344 a h
  have h2 : Entails.eval a c1349 := derived1349 a h
  have h3 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1353, some c1352, some c1341, some c1226, some c33]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c1353, c1352, c1341, c1226, c33] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c1353 := derived1353 a h
  have h1 : Entails.eval a c1352 := derived1352 a h
  have h2 : Entails.eval a c1341 := derived1341 a h
  have h3 : Entails.eval a c1226 := derived1226 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1354

end CochromaticTwenty.Certificates.B16_2_0
