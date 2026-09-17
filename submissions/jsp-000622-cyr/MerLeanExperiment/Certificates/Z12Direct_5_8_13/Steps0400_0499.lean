import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Steps0300_0399

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1303 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1294, some c52, some c963, some c30, some c1299, some c1300, some c1302, some c442, some c359, some c16, some c427, some c431, some c429, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 31) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c1246, c1294, c52, c963, c30, c1299, c1300, c1302, c442, c359, c16, c427, c431, c429] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1294 := derived1294 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1299 := derived1299 a h
  have h6 : Entails.eval a c1300 := derived1300 a h
  have h7 : Entails.eval a c1302 := derived1302 a h
  have h8 : Entails.eval a c442 := h 441 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c427 := h 426 (by decide)
  have h12 : Entails.eval a c431 := h 430 (by decide)
  have h13 : Entails.eval a c429 := h 428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1294, some c52, some c963, some c30, some c37, some c442, some c359, some c16, some c427, some c431, some c429, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1304 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 31) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c1246, c1294, c52, c963, c30, c37, c442, c359, c16, c427, c431, c429] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1294 := derived1294 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c442 := h 441 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c427 := h 426 (by decide)
  have h10 : Entails.eval a c431 := h 430 (by decide)
  have h11 : Entails.eval a c429 := h 428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c52, some c963, some c1294, some c1304, some c213, some c1303, some c597, some c404, some c98, some c484, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1305 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 31) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1246, c52, c963, c1294, c1304, c213, c1303, c597, c404, c98, c484] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c1304 := derived1304 a h
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c597 := h 596 (by decide)
  have h8 : Entails.eval a c404 := h 403 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c484 := h 483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c52, some c963, some c53, some c1294, some c30, some c1304, some c1305, some c409, some c68, some c433, some c28, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1306 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 31) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c1246, c52, c963, c53, c1294, c30, c1304, c1305, c409, c68, c433, c28] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c1294 := derived1294 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1304 := derived1304 a h
  have h7 : Entails.eval a c1305 := derived1305 a h
  have h8 : Entails.eval a c409 := h 408 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c433 := h 432 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1294, some c52, some c963, some c30, some c53, some c1303, some c1306, some c167, some c1297, some c440, some c37, some c433, some c88, some c920, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1307 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 31) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c1246, c1294, c52, c963, c30, c53, c1303, c1306, c167, c1297, c440, c37, c433, c88, c920] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1294 := derived1294 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c1306 := derived1306 a h
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c1297 := derived1297 a h
  have h10 : Entails.eval a c440 := h 439 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c433 := h 432 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c920 := derived920 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c1294, some c53, some c213, some c47, some c597, some c409, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1308 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 31) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c1246, c1307, c1294, c53, c213, c47, c597, c409] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c597 := h 596 (by decide)
  have h7 : Entails.eval a c409 := h 408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1308, some c963, some c1307, some c1294, some c409, some c597, some c406, some c70, some c46, some c59, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1309 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 31) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c1246, c1308, c963, c1307, c1294, c409, c597, c406, c70, c46, c59] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1308 := derived1308 a h
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c1294 := derived1294 a h
  have h5 : Entails.eval a c409 := h 408 (by decide)
  have h6 : Entails.eval a c597 := h 596 (by decide)
  have h7 : Entails.eval a c406 := h 405 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1307, some c1308, some c142, some c1309, some c163, some c144, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1310 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 31) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c1307, c1308, c142, c1309, c163, c144] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c1307 := derived1307 a h
  have h1 : Entails.eval a c1308 := derived1308 a h
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c1309 := derived1309 a h
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1311 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1311 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c47, some c53, some c142, some c163, some c144, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1311 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1311 : lratChecker f1311 p1311 = .success := by decide +kernel
theorem unsat1311 : Unsatisfiable (PosFin 31) f1311 := by
  apply lratCheckerSound f1311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1311
  · intro a ha; simp [p1311] at ha; subst a; trivial
  · exact checked1311
theorem derived1311 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1311 := by
  apply localUnsat_implies_entails f1311 [c1246, c1307, c47, c53, c142, c163, c144] c1311 unsat1311 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1312 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1312 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c1294, some c1311, some c266, some c1310, some c514, some c963, some c142, some c778, some c406, some c46, some c22, some c640, some c59, some c432, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1312 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1312 : lratChecker f1312 p1312 = .success := by decide +kernel
theorem unsat1312 : Unsatisfiable (PosFin 31) f1312 := by
  apply lratCheckerSound f1312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1312
  · intro a ha; simp [p1312] at ha; subst a; trivial
  · exact checked1312
theorem derived1312 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1312 := by
  apply localUnsat_implies_entails f1312 [c1246, c1307, c1294, c1311, c266, c1310, c514, c963, c142, c778, c406, c46, c22, c640, c59, c432] c1312 unsat1312 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c1311 := derived1311 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c1310 := derived1310 a h
  have h6 : Entails.eval a c514 := h 513 (by decide)
  have h7 : Entails.eval a c963 := derived963 a h
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c778 := h 777 (by decide)
  have h10 : Entails.eval a c406 := h 405 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c640 := h 639 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c432 := h 431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1313 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1313 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c1294, some c1310, some c1311, some c514, some c1312, some c30, some c472, some c534, some c428, some c621, some c22, some c704, some c241, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1313 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1313 : lratChecker f1313 p1313 = .success := by decide +kernel
theorem unsat1313 : Unsatisfiable (PosFin 31) f1313 := by
  apply lratCheckerSound f1313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1313
  · intro a ha; simp [p1313] at ha; subst a; trivial
  · exact checked1313
theorem derived1313 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1313 := by
  apply localUnsat_implies_entails f1313 [c1246, c1307, c1294, c1310, c1311, c514, c1312, c30, c472, c534, c428, c621, c22, c704, c241] c1313 unsat1313 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c1310 := derived1310 a h
  have h4 : Entails.eval a c1311 := derived1311 a h
  have h5 : Entails.eval a c514 := h 513 (by decide)
  have h6 : Entails.eval a c1312 := derived1312 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c472 := h 471 (by decide)
  have h9 : Entails.eval a c534 := h 533 (by decide)
  have h10 : Entails.eval a c428 := h 427 (by decide)
  have h11 : Entails.eval a c621 := h 620 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c704 := h 703 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1314 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨30, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c53, some c1294, some c30, some c1313, some c1307, some c213, some c307, some c1295, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1314 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 31) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c1246, c53, c1294, c30, c1313, c1307, c213, c307, c1295] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c1313 := derived1313 a h
  have h5 : Entails.eval a c1307 := derived1307 a h
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c1295 := derived1295 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1313, some c1307, some c1294, some c30, some c53, some c1314, some c597, some c409, some c1295, some c514, some c321, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1315 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 31) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c1246, c1313, c1307, c1294, c30, c53, c1314, c597, c409, c1295, c514, c321] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1313 := derived1313 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1314 := derived1314 a h
  have h7 : Entails.eval a c597 := h 596 (by decide)
  have h8 : Entails.eval a c409 := h 408 (by decide)
  have h9 : Entails.eval a c1295 := derived1295 a h
  have h10 : Entails.eval a c514 := h 513 (by decide)
  have h11 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1313, some c1307, some c1294, some c409, some c1295, some c514, some c321, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1316 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 31) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c1246, c1313, c1307, c1294, c409, c1295, c514, c321] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1313 := derived1313 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c409 := h 408 (by decide)
  have h5 : Entails.eval a c1295 := derived1295 a h
  have h6 : Entails.eval a c514 := h 513 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1313, some c1307, some c1294, some c1316, some c597, some c307, some c1295, some c70, some c404, some c1255, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1317 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 31) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c1246, c1313, c1307, c1294, c1316, c597, c307, c1295, c70, c404, c1255] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1313 := derived1313 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c1316 := derived1316 a h
  have h5 : Entails.eval a c597 := h 596 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c1295 := derived1295 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c404 := h 403 (by decide)
  have h10 : Entails.eval a c1255 := derived1255 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1317, some c1315, some c963, some c1307, some c1294, some c266, some c1313, some c409, some c70, some c406, some c59, some c38, some c147, some c574, some c666, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1318 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 31) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c1246, c1317, c1315, c963, c1307, c1294, c266, c1313, c409, c70, c406, c59, c38, c147, c574, c666] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c1315 := derived1315 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c1307 := derived1307 a h
  have h5 : Entails.eval a c1294 := derived1294 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c1313 := derived1313 a h
  have h8 : Entails.eval a c409 := h 408 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c406 := h 405 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c574 := h 573 (by decide)
  have h15 : Entails.eval a c666 := h 665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1315, some c1307, some c1294, some c266, some c1313, some c1318, some c1295, some c442, some c87, some c970, some c920, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1319 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 31) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c1246, c1315, c1307, c1294, c266, c1313, c1318, c1295, c442, c87, c970, c920] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1315 := derived1315 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c1313 := derived1313 a h
  have h6 : Entails.eval a c1318 := derived1318 a h
  have h7 : Entails.eval a c1295 := derived1295 a h
  have h8 : Entails.eval a c442 := h 441 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c970 := derived970 a h
  have h11 : Entails.eval a c920 := derived920 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1315, some c1307, some c1294, some c266, some c1313, some c409, some c514, some c87, some c778, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1320 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 31) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c1246, c1315, c1307, c1294, c266, c1313, c409, c514, c87, c778] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1315 := derived1315 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c1313 := derived1313 a h
  have h6 : Entails.eval a c409 := h 408 (by decide)
  have h7 : Entails.eval a c514 := h 513 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c778 := h 777 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c1294, some c1315, some c963, some c1320, some c597, some c406, some c1319, some c29, some c418, some c305, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1321 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 31) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c1246, c1307, c1294, c1315, c963, c1320, c597, c406, c1319, c29, c418, c305] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c1315 := derived1315 a h
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c1320 := derived1320 a h
  have h6 : Entails.eval a c597 := h 596 (by decide)
  have h7 : Entails.eval a c406 := h 405 (by decide)
  have h8 : Entails.eval a c1319 := derived1319 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c418 := h 417 (by decide)
  have h11 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1321, some c1313, some c1307, some c1294, some c1314, some c163, some c107, some c442, some c87, some c896, some c725, some c970, some c307, some c967, some c661, some c38, some c521, some c404, some c121, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1322 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 31) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c1246, c1321, c1313, c1307, c1294, c1314, c163, c107, c442, c87, c896, c725, c970, c307, c967, c661, c38, c521, c404, c121] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1321 := derived1321 a h
  have h2 : Entails.eval a c1313 := derived1313 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c1294 := derived1294 a h
  have h5 : Entails.eval a c1314 := derived1314 a h
  have h6 : Entails.eval a c163 := h 162 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c442 := h 441 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c896 := h 895 (by decide)
  have h11 : Entails.eval a c725 := h 724 (by decide)
  have h12 : Entails.eval a c970 := derived970 a h
  have h13 : Entails.eval a c307 := h 306 (by decide)
  have h14 : Entails.eval a c967 := derived967 a h
  have h15 : Entails.eval a c661 := h 660 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c521 := h 520 (by decide)
  have h18 : Entails.eval a c404 := h 403 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c1321, some c163, some c963, some c1322, some c1313, some c1294, some c694, some c29, some c113, some c635, some c637, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1323 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 31) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1246, c1307, c1321, c163, c963, c1322, c1313, c1294, c694, c29, c113, c635, c637] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c1321 := derived1321 a h
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c1322 := derived1322 a h
  have h6 : Entails.eval a c1313 := derived1313 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c694 := h 693 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c635 := h 634 (by decide)
  have h12 : Entails.eval a c637 := h 636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨30, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1322, some c1321, some c1307, some c1294, some c1323, some c367, some c259, some c435, some c637, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1324 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 31) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1246, c1322, c1321, c1307, c1294, c1323, c367, c259, c435, c637] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1322 := derived1322 a h
  have h2 : Entails.eval a c1321 := derived1321 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c1294 := derived1294 a h
  have h5 : Entails.eval a c1323 := derived1323 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c259 := h 258 (by decide)
  have h8 : Entails.eval a c435 := h 434 (by decide)
  have h9 : Entails.eval a c637 := h 636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1322, some c1321, some c1313, some c1307, some c963, some c163, some c1324, some c99, some c34, some c680, some c711, some c279, some c278, some c57, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1325 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 31) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c1322, c1321, c1313, c1307, c963, c163, c1324, c99, c34, c680, c711, c279, c278, c57] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c1322 := derived1322 a h
  have h1 : Entails.eval a c1321 := derived1321 a h
  have h2 : Entails.eval a c1313 := derived1313 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c1324 := derived1324 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c680 := h 679 (by decide)
  have h10 : Entails.eval a c711 := h 710 (by decide)
  have h11 : Entails.eval a c279 := h 278 (by decide)
  have h12 : Entails.eval a c278 := h 277 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1307, some c1325, some c53, some c54, some c1322, some c1313, some c1294, some c98, some c147, some c802, some c803, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1326 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 31) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c1246, c1307, c1325, c53, c54, c1322, c1313, c1294, c98, c147, c802, c803] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c1322 := derived1322 a h
  have h6 : Entails.eval a c1313 := derived1313 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c802 := h 801 (by decide)
  have h11 : Entails.eval a c803 := h 802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1326, some c1307, some c1325, some c53, some c54, some c1322, some c1321, some c147, some c583, some c755, some c374, some c143, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1327 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 31) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c1246, c1326, c1307, c1325, c53, c54, c1322, c1321, c147, c583, c755, c374, c143] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1326 := derived1326 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c1322 := derived1322 a h
  have h7 : Entails.eval a c1321 := derived1321 a h
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c583 := h 582 (by decide)
  have h10 : Entails.eval a c755 := h 754 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1294, some c1307, some c1313, some c1322, some c1325, some c30, some c53, some c54, some c1326, some c1327, some c532, some c157, some c71, some c310, some c33, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1328 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 31) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c1246, c1294, c1307, c1313, c1322, c1325, c30, c53, c54, c1326, c1327, c532, c157, c71, c310, c33] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1294 := derived1294 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1313 := derived1313 a h
  have h4 : Entails.eval a c1322 := derived1322 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c1326 := derived1326 a h
  have h10 : Entails.eval a c1327 := derived1327 a h
  have h11 : Entails.eval a c532 := h 531 (by decide)
  have h12 : Entails.eval a c157 := h 156 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c144, some c903, some c877, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1329 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 31) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c1328, c144, c903, c877] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c903 := derived903 a h
  have h3 : Entails.eval a c877 := h 876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c84, some c203, some c847, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1330 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 31) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c1328, c84, c203, c847] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c847 := h 846 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1330, some c767, some c1329, some c28, some c877, some c542, some c239, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1331 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 31) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c1246, c1330, c767, c1329, c28, c877, c542, c239] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1330 := derived1330 a h
  have h2 : Entails.eval a c767 := h 766 (by decide)
  have h3 : Entails.eval a c1329 := derived1329 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c877 := h 876 (by decide)
  have h6 : Entails.eval a c542 := h 541 (by decide)
  have h7 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c229, some c327, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1332 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 31) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c1246, c1328, c229, c327] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1330, some c767, some c1331, some c1332, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1333 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 31) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c1330, c767, c1331, c1332] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c1330 := derived1330 a h
  have h1 : Entails.eval a c767 := h 766 (by decide)
  have h2 : Entails.eval a c1331 := derived1331 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c204, some c1332, some c27, some c209, some c870, some c353, some c532, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1334 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 31) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c1328, c1246, c204, c1332, c27, c209, c870, c353, c532] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c870 := h 869 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c532 := h 531 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1333, some c1334, some c1329, some c767, some c84, some c67, some c897, some c115, some c532, some c451, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1335 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 31) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c1328, c1246, c1333, c1334, c1329, c767, c84, c67, c897, c115, c532, c451] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1333 := derived1333 a h
  have h3 : Entails.eval a c1334 := derived1334 a h
  have h4 : Entails.eval a c1329 := derived1329 a h
  have h5 : Entails.eval a c767 := h 766 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c897 := h 896 (by decide)
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c532 := h 531 (by decide)
  have h11 : Entails.eval a c451 := h 450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c84, some c203, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1336 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 31) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1328, c84, c203] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1333, some c1334, some c1329, some c1335, some c1336, some c28, some c877, some c411, some c353, some c115, some c370, some c530, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1337 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 31) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c1328, c1246, c1333, c1334, c1329, c1335, c1336, c28, c877, c411, c353, c115, c370, c530] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1333 := derived1333 a h
  have h3 : Entails.eval a c1334 := derived1334 a h
  have h4 : Entails.eval a c1329 := derived1329 a h
  have h5 : Entails.eval a c1335 := derived1335 a h
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c877 := h 876 (by decide)
  have h9 : Entails.eval a c411 := h 410 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c530 := h 529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1332, some c1336, some c28, some c877, some c608, some c1205, some c112, some c56, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1338 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 31) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c1328, c1332, c1336, c28, c877, c608, c1205, c112, c56] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1336 := derived1336 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c877 := h 876 (by decide)
  have h5 : Entails.eval a c608 := h 607 (by decide)
  have h6 : Entails.eval a c1205 := derived1205 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1337, some c1338, some c767, some c67, some c897, some c594, some c451, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 31) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c1246, c1328, c1337, c1338, c767, c67, c897, c594, c451] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1337 := derived1337 a h
  have h3 : Entails.eval a c1338 := derived1338 a h
  have h4 : Entails.eval a c767 := h 766 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c897 := h 896 (by decide)
  have h7 : Entails.eval a c594 := h 593 (by decide)
  have h8 : Entails.eval a c451 := h 450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1339, some c767, some c84, some c64, some c67, some c112, some c788, some c515, some c703, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1340 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 31) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1328, c1246, c1339, c767, c84, c64, c67, c112, c788, c515, c703] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1339 := derived1339 a h
  have h3 : Entails.eval a c767 := h 766 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c788 := h 787 (by decide)
  have h9 : Entails.eval a c515 := h 514 (by decide)
  have h10 : Entails.eval a c703 := h 702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1340, some c1332, some c1336, some c1338, some c1329, some c28, some c877, some c411, some c1333, some c240, some c353, some c1205, some c543, some c423, some c581, some c325, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 31) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c1328, c1246, c1340, c1332, c1336, c1338, c1329, c28, c877, c411, c1333, c240, c353, c1205, c543, c423, c581, c325] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1336 := derived1336 a h
  have h5 : Entails.eval a c1338 := derived1338 a h
  have h6 : Entails.eval a c1329 := derived1329 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c877 := h 876 (by decide)
  have h9 : Entails.eval a c411 := h 410 (by decide)
  have h10 : Entails.eval a c1333 := derived1333 a h
  have h11 : Entails.eval a c240 := h 239 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c1205 := derived1205 a h
  have h14 : Entails.eval a c543 := h 542 (by decide)
  have h15 : Entails.eval a c423 := h 422 (by decide)
  have h16 : Entails.eval a c581 := h 580 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c139, some c203, some c33, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1342 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 31) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c1328, c139, c203, c33] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1332, some c1342, some c793, some c608, some c146, some c112, some c170, some c33, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1343 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 31) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c1328, c1332, c1342, c793, c608, c146, c112, c170, c33] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1342 := derived1342 a h
  have h3 : Entails.eval a c793 := h 792 (by decide)
  have h4 : Entails.eval a c608 := h 607 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c28, some c608, some c353, some c736, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1344 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 31) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1328, c28, c608, c353, c736] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c608 := h 607 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c736 := h 735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c788, some c870, some c80, some c703, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1345 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 31) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c788, c870, c80, c703] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c788 := h 787 (by decide)
  have h1 : Entails.eval a c870 := h 869 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c703 := h 702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1341, some c1343, some c1345, some c82, some c204, some c1344, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1346 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 31) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c1328, c1341, c1343, c1345, c82, c204, c1344] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1341 := derived1341 a h
  have h2 : Entails.eval a c1343 := derived1343 a h
  have h3 : Entails.eval a c1345 := derived1345 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c1344 := derived1344 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1343, some c139, some c82, some c91, some c155, some c703, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 31) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c1328, c1343, c139, c82, c91, c155, c703] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1343 := derived1343 a h
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c703 := h 702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1341, some c1343, some c1346, some c1347, some c793, some c204, some c755, some c209, some c571, some c126, some c515, some c521, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1348 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 31) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c1246, c1328, c1341, c1343, c1346, c1347, c793, c204, c755, c209, c571, c126, c515, c521] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1341 := derived1341 a h
  have h3 : Entails.eval a c1343 := derived1343 a h
  have h4 : Entails.eval a c1346 := derived1346 a h
  have h5 : Entails.eval a c1347 := derived1347 a h
  have h6 : Entails.eval a c793 := h 792 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c755 := h 754 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c571 := h 570 (by decide)
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c515 := h 514 (by decide)
  have h13 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c515, some c521, some c519, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1349 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 31) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c1246, c515, c521, c519] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c515 := h 514 (by decide)
  have h2 : Entails.eval a c521 := h 520 (by decide)
  have h3 : Entails.eval a c519 := h 518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c204, some c209, some c515, some c1349, some c17, some c126, some c692, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 31) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c1328, c1246, c204, c209, c515, c1349, c17, c126, c692] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c515 := h 514 (by decide)
  have h5 : Entails.eval a c1349 := derived1349 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c692 := h 691 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c209, some c515, some c1349, some c126, some c25, some c692, some c301, some c967, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1351 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 31) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1328, c1246, c209, c515, c1349, c126, c25, c692, c301, c967] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c515 := h 514 (by decide)
  have h4 : Entails.eval a c1349 := derived1349 a h
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c692 := h 691 (by decide)
  have h8 : Entails.eval a c301 := h 300 (by decide)
  have h9 : Entails.eval a c967 := derived967 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1348, some c1350, some c1351, some c82, some c75, some c121, some c28, some c411, some c609, some c615, some c470, some c96, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1352 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 31) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c1328, c1246, c1348, c1350, c1351, c82, c75, c121, c28, c411, c609, c615, c470, c96] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1348 := derived1348 a h
  have h3 : Entails.eval a c1350 := derived1350 a h
  have h4 : Entails.eval a c1351 := derived1351 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c411 := h 410 (by decide)
  have h10 : Entails.eval a c609 := h 608 (by decide)
  have h11 : Entails.eval a c615 := h 614 (by decide)
  have h12 : Entails.eval a c470 := h 469 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨24, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c82, some c204, some c75, some c121, some c28, some c61, some c493, some c312, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1353 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 31) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1328, c1246, c82, c204, c75, c121, c28, c61, c493, c312] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c493 := h 492 (by decide)
  have h9 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c556, some c614, some c627, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1354 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 31) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c556, c614, c627] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c556 := h 555 (by decide)
  have h1 : Entails.eval a c614 := h 613 (by decide)
  have h2 : Entails.eval a c627 := h 626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1353, some c28, some c1354, some c146, some c112, some c170, some c80, some c164, some c178, some c781, some c50, some c1280, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1355 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 31) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c1328, c1353, c28, c1354, c146, c112, c170, c80, c164, c178, c781, c50, c1280] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1353 := derived1353 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c1354 := derived1354 a h
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c781 := h 780 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c1280 := derived1280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1353, some c209, some c1355, some c139, some c91, some c557, some c709, some c271, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1356 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 31) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c1328, c1353, c209, c1355, c139, c91, c557, c709, c271] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1353 := derived1353 a h
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c1355 := derived1355 a h
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c557 := h 556 (by decide)
  have h7 : Entails.eval a c709 := h 708 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c209, some c91, some c61, some c557, some c709, some c218, some c516, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1357 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 31) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c1328, c209, c91, c61, c557, c709, c218, c516] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c557 := h 556 (by decide)
  have h5 : Entails.eval a c709 := h 708 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c516 := h 515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c61, some c556, some c217, some c578, some c25, some c135, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1358 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 31) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c1246, c61, c556, c217, c578, c25, c135] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c556 := h 555 (by decide)
  have h3 : Entails.eval a c217 := h 216 (by decide)
  have h4 : Entails.eval a c578 := h 577 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1348, some c1352, some c1353, some c209, some c1356, some c1357, some c1358, some c257, some c146, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1359 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 31) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c1348, c1352, c1353, c209, c1356, c1357, c1358, c257, c146] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1352 := derived1352 a h
  have h2 : Entails.eval a c1353 := derived1353 a h
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c1356 := derived1356 a h
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c1358 := derived1358 a h
  have h7 : Entails.eval a c257 := h 256 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c705, some c872, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 31) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c209, c705, c872] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c209 := h 208 (by decide)
  have h1 : Entails.eval a c705 := h 704 (by decide)
  have h2 : Entails.eval a c872 := h 871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c209, some c1360, some c56, some c112, some c710, some c709, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 31) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c1328, c1246, c209, c1360, c56, c112, c710, c709] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c1360 := derived1360 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c710 := h 709 (by decide)
  have h7 : Entails.eval a c709 := h 708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1348, some c1359, some c1361, some c204, some c82, some c1354, some c112, some c56, some c744, some c799, some c72, some c149, some c698, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1362 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 31) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c1328, c1246, c1348, c1359, c1361, c204, c82, c1354, c112, c56, c744, c799, c72, c149, c698] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1348 := derived1348 a h
  have h3 : Entails.eval a c1359 := derived1359 a h
  have h4 : Entails.eval a c1361 := derived1361 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c1354 := derived1354 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c744 := h 743 (by decide)
  have h11 : Entails.eval a c799 := h 798 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c149 := h 148 (by decide)
  have h14 : Entails.eval a c698 := h 697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1348, some c1359, some c1361, some c82, some c204, some c28, some c1362, some c65, some c56, some c738, some c297, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1363 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 31) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1328, c1348, c1359, c1361, c82, c204, c28, c1362, c65, c56, c738, c297] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1348 := derived1348 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c1361 := derived1361 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c1362 := derived1362 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c738 := h 737 (by decide)
  have h11 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1363, some c1332, some c1348, some c67, some c71, some c302, some c28, some c335, some c880, some c326, some c176, some c794, some c271, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1364 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 31) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c1328, c1363, c1332, c1348, c67, c71, c302, c28, c335, c880, c326, c176, c794, c271] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1363 := derived1363 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1348 := derived1348 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c335 := h 334 (by decide)
  have h9 : Entails.eval a c880 := h 879 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c794 := h 793 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1332, some c28, some c1354, some c610, some c879, some c312, some c456, some c492, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1365 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 31) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c1328, c1332, c28, c1354, c610, c879, c312, c456, c492] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c1354 := derived1354 a h
  have h4 : Entails.eval a c610 := h 609 (by decide)
  have h5 : Entails.eval a c879 := h 878 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c456 := h 455 (by decide)
  have h8 : Entails.eval a c492 := h 491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c819, some c232, some c639, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1366 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 31) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c819, c232, c639] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c819 := h 818 (by decide)
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c639 := h 638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1364, some c1363, some c1348, some c1366, some c752, some c1365, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1367 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 31) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c1364, c1363, c1348, c1366, c752, c1365] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c1364 := derived1364 a h
  have h1 : Entails.eval a c1363 := derived1363 a h
  have h2 : Entails.eval a c1348 := derived1348 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c752 := h 751 (by decide)
  have h5 : Entails.eval a c1365 := derived1365 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c28, some c578, some c615, some c3, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1368 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 31) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c1246, c28, c578, c615, c3] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c578 := h 577 (by decide)
  have h3 : Entails.eval a c615 := h 614 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1348, some c1363, some c1332, some c1364, some c1367, some c1368, some c82, some c232, some c1336, some c139, some c91, some c822, some c554, some c743, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1369 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 31) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c1328, c1348, c1363, c1332, c1364, c1367, c1368, c82, c232, c1336, c139, c91, c822, c554, c743] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1348 := derived1348 a h
  have h2 : Entails.eval a c1363 := derived1363 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1364 := derived1364 a h
  have h5 : Entails.eval a c1367 := derived1367 a h
  have h6 : Entails.eval a c1368 := derived1368 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c1336 := derived1336 a h
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c822 := h 821 (by decide)
  have h13 : Entails.eval a c554 := h 553 (by decide)
  have h14 : Entails.eval a c743 := h 742 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1369, some c82, some c203, some c232, some c1336, some c139, some c91, some c686, some c593, some c504, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1370 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 31) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c1328, c1369, c82, c203, c232, c1336, c139, c91, c686, c593, c504] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1369 := derived1369 a h
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c686 := h 685 (by decide)
  have h9 : Entails.eval a c593 := h 592 (by decide)
  have h10 : Entails.eval a c504 := h 503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1332, some c62, some c302, some c335, some c26, some c326, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1371 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 31) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c1328, c1332, c62, c302, c335, c26, c326] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c12, some c3, some c38, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1372 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 31) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c1246, c12, c3, c38] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1332, some c1369, some c1370, some c28, some c1371, some c1354, some c112, some c1372, some c1365, some c578, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1373 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 31) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c1328, c1246, c1332, c1369, c1370, c28, c1371, c1354, c112, c1372, c1365, c578] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1369 := derived1369 a h
  have h4 : Entails.eval a c1370 := derived1370 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1371 := derived1371 a h
  have h7 : Entails.eval a c1354 := derived1354 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c1372 := derived1372 a h
  have h10 : Entails.eval a c1365 := derived1365 a h
  have h11 : Entails.eval a c578 := h 577 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c28, some c578, some c1133, some c1205, some c402, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1374 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 31) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c1246, c28, c578, c1133, c1205, c402] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c578 := h 577 (by decide)
  have h3 : Entails.eval a c1133 := derived1133 a h
  have h4 : Entails.eval a c1205 := derived1205 a h
  have h5 : Entails.eval a c402 := h 401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c28, some c1374, some c12, some c38, some c306, some c307, some c37, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1375 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 31) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c1246, c28, c1374, c12, c38, c306, c307, c37] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c1374 := derived1374 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1373, some c1332, some c1369, some c28, some c1375, some c62, some c302, some c49, some c26, some c336, some c326, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1376 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 31) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c1328, c1373, c1332, c1369, c28, c1375, c62, c302, c49, c26, c336, c326] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1373 := derived1373 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1369 := derived1369 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c1375 := derived1375 a h
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c336 := h 335 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1369, some c1373, some c1376, some c82, some c203, some c232, some c1336, some c139, some c91, some c48, some c690, some c686, some c400, some c504, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1377 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 31) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c1328, c1369, c1373, c1376, c82, c203, c232, c1336, c139, c91, c48, c690, c686, c400, c504] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1369 := derived1369 a h
  have h2 : Entails.eval a c1373 := derived1373 a h
  have h3 : Entails.eval a c1376 := derived1376 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c1336 := derived1336 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c48 := h 47 (by decide)
  have h11 : Entails.eval a c690 := h 689 (by decide)
  have h12 : Entails.eval a c686 := h 685 (by decide)
  have h13 : Entails.eval a c400 := h 399 (by decide)
  have h14 : Entails.eval a c504 := h 503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨2, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c305, some c237, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1378 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 31) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c1328, c305, c237] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨2, by decide⟩, true), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c82, some c67, some c1378, some c38, some c307, some c806, some c313, some c791, some c54, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 31) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c1328, c1246, c82, c67, c1378, c38, c307, c806, c313, c791, c54] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c1378 := derived1378 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c806 := h 805 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c791 := h 790 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1377, some c1369, some c67, some c1379, some c37, some c213, some c70, some c306, some c38, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1380 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 31) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c1328, c1246, c1377, c1369, c67, c1379, c37, c213, c70, c306, c38] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1377 := derived1377 a h
  have h3 : Entails.eval a c1369 := derived1369 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c1379 := derived1379 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c306 := h 305 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c37, some c38, some c70, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 31) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c1246, c37, c38, c70] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1380, some c1377, some c1369, some c51, some c1381, some c209, some c204, some c140, some c586, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1382 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 31) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c1328, c1380, c1377, c1369, c51, c1381, c209, c204, c140, c586] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c1377 := derived1377 a h
  have h3 : Entails.eval a c1369 := derived1369 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c1381 := derived1381 a h
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c586 := h 585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1380, some c1377, some c1369, some c62, some c71, some c209, some c236, some c204, some c121, some c1133, some c744, some c850, some c849, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1383 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 31) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1328, c1380, c1377, c1369, c62, c71, c209, c236, c204, c121, c1133, c744, c850, c849] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c1377 := derived1377 a h
  have h3 : Entails.eval a c1369 := derived1369 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c1133 := derived1133 a h
  have h11 : Entails.eval a c744 := h 743 (by decide)
  have h12 : Entails.eval a c850 := h 849 (by decide)
  have h13 : Entails.eval a c849 := h 848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1369, some c1382, some c1383, some c37, some c213, some c306, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1384 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 31) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c1246, c1369, c1382, c1383, c37, c213, c306] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1369 := derived1369 a h
  have h2 : Entails.eval a c1382 := derived1382 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c213, some c70, some c306, some c38, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1385 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 31) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c1246, c213, c70, c306, c38] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c213 := h 212 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1384, some c1380, some c1377, some c1369, some c1375, some c1385, some c217, some c307, some c51, some c38, some c8, some c561, some c541, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1386 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 31) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c1246, c1328, c1384, c1380, c1377, c1369, c1375, c1385, c217, c307, c51, c38, c8, c561, c541] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1384 := derived1384 a h
  have h3 : Entails.eval a c1380 := derived1380 a h
  have h4 : Entails.eval a c1377 := derived1377 a h
  have h5 : Entails.eval a c1369 := derived1369 a h
  have h6 : Entails.eval a c1375 := derived1375 a h
  have h7 : Entails.eval a c1385 := derived1385 a h
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c561 := h 560 (by decide)
  have h14 : Entails.eval a c541 := h 540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1369, some c1377, some c1380, some c1384, some c1386, some c62, some c71, some c209, some c236, some c121, some c829, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1387 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 31) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c1328, c1369, c1377, c1380, c1384, c1386, c62, c71, c209, c236, c121, c829] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1369 := derived1369 a h
  have h2 : Entails.eval a c1377 := derived1377 a h
  have h3 : Entails.eval a c1380 := derived1380 a h
  have h4 : Entails.eval a c1384 := derived1384 a h
  have h5 : Entails.eval a c1386 := derived1386 a h
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c829 := h 828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c62, some c305, some c1154, some c368, some c463, some c129, some c707, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1388 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 31) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c1328, c62, c305, c1154, c368, c463, c129, c707] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c1154 := derived1154 a h
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c463 := h 462 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c707 := h 706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c62, some c1387, some c1388, some c236, some c237, some c82, some c25, some c247, some c10, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1389 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 31) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c1328, c62, c1387, c1388, c236, c237, c82, c25, c247, c10] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c1388 := derived1388 a h
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c237 := h 236 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1389, some c1332, some c586, some c394, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1390 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 31) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c1328, c1389, c1332, c586, c394] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1389 := derived1389 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c586 := h 585 (by decide)
  have h4 : Entails.eval a c394 := h 393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1391 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c62, some c1389, some c1332, some c1390, some c92, some c1336, some c26, some c28, some c103, some c274, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1391 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 31) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c1328, c62, c1389, c1332, c1390, c92, c1336, c26, c28, c103, c274] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c1389 := derived1389 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1390 := derived1390 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨21, by decide⟩, false), (⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c26, some c28, some c210, some c816, some c632, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1392 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 31) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c1328, c26, c28, c210, c816, c632] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c816 := h 815 (by decide)
  have h5 : Entails.eval a c632 := h 631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1393 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1393 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1392, some c116, some c84, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1393 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1393 : lratChecker f1393 p1393 = .success := by decide +kernel
theorem unsat1393 : Unsatisfiable (PosFin 31) f1393 := by
  apply lratCheckerSound f1393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1393
  · intro a ha; simp [p1393] at ha; subst a; trivial
  · exact checked1393
theorem derived1393 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1393 := by
  apply localUnsat_implies_entails f1393 [c1328, c1392, c116, c84] c1393 unsat1393 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1392 := derived1392 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1394 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1391, some c62, some c1387, some c1393, some c85, some c431, some c586, some c854, some c306, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1394 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 31) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c1328, c1246, c1391, c62, c1387, c1393, c85, c431, c586, c854, c306] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1391 := derived1391 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c1393 := derived1393 a h
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c431 := h 430 (by decide)
  have h8 : Entails.eval a c586 := h 585 (by decide)
  have h9 : Entails.eval a c854 := h 853 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1387, some c85, some c431, some c25, some c1280, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1395 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 31) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c1328, c1246, c1387, c85, c431, c25, c1280] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c431 := h 430 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c1280 := derived1280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c25, some c702, some c65, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1396 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 31) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c1246, c1328, c25, c702, c65] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c702 := h 701 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1391, some c62, some c1394, some c1332, some c683, some c1395, some c1396, some c10, some c1280, some c537, some c213, some c116, some c429, some c396, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1397 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 31) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c1328, c1246, c1391, c62, c1394, c1332, c683, c1395, c1396, c10, c1280, c537, c213, c116, c429, c396] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1391 := derived1391 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c1394 := derived1394 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c683 := h 682 (by decide)
  have h7 : Entails.eval a c1395 := derived1395 a h
  have h8 : Entails.eval a c1396 := derived1396 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c1280 := derived1280 a h
  have h11 : Entails.eval a c537 := h 536 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c429 := h 428 (by decide)
  have h15 : Entails.eval a c396 := h 395 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1387, some c62, some c1391, some c1397, some c92, some c85, some c194, some c193, some c104, some c139, some c50, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1398 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 31) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c1246, c1328, c1387, c62, c1391, c1397, c92, c85, c194, c193, c104, c139, c50] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c1391 := derived1391 a h
  have h5 : Entails.eval a c1397 := derived1397 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1398, some c1385, some c37, some c1387, some c80, some c60, some c428, some c46, some c274, some c601, some c782, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 31) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c1246, c1398, c1385, c37, c1387, c80, c60, c428, c46, c274, c601, c782] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1398 := derived1398 a h
  have h2 : Entails.eval a c1385 := derived1385 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c428 := h 427 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c601 := h 600 (by decide)
  have h11 : Entails.eval a c782 := h 781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1398, some c1385, some c37, some c1387, some c1399, some c85, some c830, some c132, some c692, some c131, some c1058, some c165, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1400 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 31) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c1246, c1328, c1398, c1385, c37, c1387, c1399, c85, c830, c132, c692, c131, c1058, c165] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1398 := derived1398 a h
  have h3 : Entails.eval a c1385 := derived1385 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1387 := derived1387 a h
  have h6 : Entails.eval a c1399 := derived1399 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c830 := h 829 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c692 := h 691 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c1058 := derived1058 a h
  have h13 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c85, some c37, some c1349, some c89, some c187, some c1332, some c328, some c643, some c587, some c550, some c564, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1401 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 31) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c1246, c1328, c85, c37, c1349, c89, c187, c1332, c328, c643, c587, c550, c564] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1349 := derived1349 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c1332 := derived1332 a h
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c643 := h 642 (by decide)
  have h10 : Entails.eval a c587 := h 586 (by decide)
  have h11 : Entails.eval a c550 := h 549 (by decide)
  have h12 : Entails.eval a c564 := h 563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1400, some c1398, some c1385, some c37, some c1387, some c85, some c1401, some c59, some c305, some c212, some c207, some c513, some c533, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1402 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 31) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c1246, c1328, c1400, c1398, c1385, c37, c1387, c85, c1401, c59, c305, c212, c207, c513, c533] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1400 := derived1400 a h
  have h3 : Entails.eval a c1398 := derived1398 a h
  have h4 : Entails.eval a c1385 := derived1385 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c1387 := derived1387 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1401 := derived1401 a h
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c513 := h 512 (by decide)
  have h14 : Entails.eval a c533 := h 532 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1402

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
