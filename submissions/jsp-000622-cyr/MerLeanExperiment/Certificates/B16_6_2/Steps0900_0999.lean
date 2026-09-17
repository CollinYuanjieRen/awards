import MerLeanExperiment.Certificates.B16_6_2.Steps0800_0899

/-! Generated from the actual pinned b16_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1293 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c20, some c228, some c106, some c107, some c1224, some c783, some c79, some c39, some c254, some c490, some c306, some c17, some c1221, some c218, some c292, some c291, some c72, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 57) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c1211, c20, c228, c106, c107, c1224, c783, c79, c39, c254, c490, c306, c17, c1221, c218, c292, c291, c72] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1224 := derived1224 a h
  have h6 : Entails.eval a c783 := derived783 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c490 := derived490 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c1221 := derived1221 a h
  have h14 : Entails.eval a c218 := h 217 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c59, some c127, some c186, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p1294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 57) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c59, c127, c186] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c127 := h 126 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c1211, some c107, some c1287, some c1292, some c4, some c113, some c1293, some c255, some c1294, some c20, some c228, some c292, some c1221, some c976, some c328, some c150, some c1219, some c215, some c207, some c208, some c261, some c136, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 57) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c1224, c1211, c107, c1287, c1292, c4, c113, c1293, c255, c1294, c20, c228, c292, c1221, c976, c328, c150, c1219, c215, c207, c208, c261, c136] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1292 := derived1292 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c1293 := derived1293 a h
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c1294 := derived1294 a h
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c1221 := derived1221 a h
  have h14 : Entails.eval a c976 := derived976 a h
  have h15 : Entails.eval a c328 := h 327 (by decide)
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c1219 := derived1219 a h
  have h18 : Entails.eval a c215 := h 214 (by decide)
  have h19 : Entails.eval a c207 := h 206 (by decide)
  have h20 : Entails.eval a c208 := h 207 (by decide)
  have h21 : Entails.eval a c261 := h 260 (by decide)
  have h22 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1287, some c1211, some c1292, some c4, some c113, some c1293, some c255, some c20, some c106, some c107, some c1224, some c1295, some c52, some c119, some c208, some c186, some c1003, some c150, some c92, some c1014, some c1222, some c302, some c383, some c1221, some c37, some c1223, some c249, some c17, some c111, some c1047, some c98, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 57) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c1287, c1211, c1292, c4, c113, c1293, c255, c20, c106, c107, c1224, c1295, c52, c119, c208, c186, c1003, c150, c92, c1014, c1222, c302, c383, c1221, c37, c1223, c249, c17, c111, c1047, c98] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c1287 := derived1287 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1292 := derived1292 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c1293 := derived1293 a h
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c1224 := derived1224 a h
  have h11 : Entails.eval a c1295 := derived1295 a h
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c1003 := derived1003 a h
  have h17 : Entails.eval a c150 := h 149 (by decide)
  have h18 : Entails.eval a c92 := h 91 (by decide)
  have h19 : Entails.eval a c1014 := derived1014 a h
  have h20 : Entails.eval a c1222 := derived1222 a h
  have h21 : Entails.eval a c302 := h 301 (by decide)
  have h22 : Entails.eval a c383 := h 382 (by decide)
  have h23 : Entails.eval a c1221 := derived1221 a h
  have h24 : Entails.eval a c37 := h 36 (by decide)
  have h25 : Entails.eval a c1223 := derived1223 a h
  have h26 : Entails.eval a c249 := h 248 (by decide)
  have h27 : Entails.eval a c17 := h 16 (by decide)
  have h28 : Entails.eval a c111 := h 110 (by decide)
  have h29 : Entails.eval a c1047 := derived1047 a h
  have h30 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨9, by decide⟩, true), (⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c149, some c8, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 57) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c45, c149, c8] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1298 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c8, some c22, some c192, some c132, some c389, some c17, some c102, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 57) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c106, c8, c22, c192, c132, c389, c17, c102] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c389 := h 388 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨32, by decide⟩, true), (⟨52, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c388, some c1011, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 57) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c389, c388, c1011] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c1011 := derived1011 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c113, some c20, some c106, some c107, some c1287, some c52, some c1297, some c1151, some c325, some c326, some c217, some c48, some c151, some c1298, some c1299, some c96, some c192, some c17, some c205, some c138, some c198, some c254, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 57) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c4, c113, c20, c106, c107, c1287, c52, c1297, c1151, c325, c326, c217, c48, c151, c1298, c1299, c96, c192, c17, c205, c138, c198, c254] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c1297 := derived1297 a h
  have h8 : Entails.eval a c1151 := derived1151 a h
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c217 := h 216 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c1298 := derived1298 a h
  have h15 : Entails.eval a c1299 := derived1299 a h
  have h16 : Entails.eval a c96 := h 95 (by decide)
  have h17 : Entails.eval a c192 := h 191 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c138 := h 137 (by decide)
  have h21 : Entails.eval a c198 := h 197 (by decide)
  have h22 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c1211, some c107, some c1292, some c4, some c113, some c20, some c228, some c1296, some c145, some c1300, some c306, some c328, some c59, some c292, some c290, some c976, some c1219, some c1109, some c388, some c192, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 57) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c1224, c1211, c107, c1292, c4, c113, c20, c228, c1296, c145, c1300, c306, c328, c59, c292, c290, c976, c1219, c1109, c388, c192] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1292 := derived1292 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c1296 := derived1296 a h
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c1300 := derived1300 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c290 := h 289 (by decide)
  have h16 : Entails.eval a c976 := derived976 a h
  have h17 : Entails.eval a c1219 := derived1219 a h
  have h18 : Entails.eval a c1109 := derived1109 a h
  have h19 : Entails.eval a c388 := h 387 (by decide)
  have h20 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨41, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1287, some c192, some c142, some c173, some c1060, some c161, some c207, some c151, some c163, some c282, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 57) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c1287, c192, c142, c173, c1060, c161, c207, c151, c163, c282] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c1287 := derived1287 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c173 := h 172 (by decide)
  have h4 : Entails.eval a c1060 := derived1060 a h
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c151 := h 150 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1303 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false), (⟨47, by decide⟩, true), (⟨29, by decide⟩, false), (⟨16, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1301, some c1224, some c1211, some c1287, some c79, some c59, some c343, some c53, some c1302, some c8, some c96, some c111, some c88, some c43, some c304, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 57) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c1301, c1224, c1211, c1287, c79, c59, c343, c53, c1302, c8, c96, c111, c88, c43, c304] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1224 := derived1224 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c1302 := derived1302 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1301, some c1224, some c1211, some c1215, some c1221, some c976, some c306, some c328, some c42, some c1219, some c388, some c1303, some c112, some c96, some c110, some c108, some c102, some c43, some c304, some c56, some c353, some c1057, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 57) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c1301, c1224, c1211, c1215, c1221, c976, c306, c328, c42, c1219, c388, c1303, c112, c96, c110, c108, c102, c43, c304, c56, c353, c1057] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1224 := derived1224 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1215 := derived1215 a h
  have h4 : Entails.eval a c1221 := derived1221 a h
  have h5 : Entails.eval a c976 := derived976 a h
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1219 := derived1219 a h
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c1303 := derived1303 a h
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c108 := h 107 (by decide)
  have h16 : Entails.eval a c102 := h 101 (by decide)
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c304 := h 303 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c1057 := derived1057 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1301, some c1224, some c1211, some c112, some c37, some c96, some c110, some c108, some c102, some c43, some c304, some c56, some c353, some c1057, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 57) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1301, c1224, c1211, c112, c37, c96, c110, c108, c102, c43, c304, c56, c353, c1057] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1224 := derived1224 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c1057 := derived1057 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1304, some c1301, some c1305, some c42, some c328, some c145, some c37, some c312, some c326, some c324, some c318, some c43, some c12, some c116, some c1047, some c28, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 57) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c1304, c1301, c1305, c42, c328, c145, c37, c312, c326, c324, c318, c43, c12, c116, c1047, c28] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c1304 := derived1304 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1305 := derived1305 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c1047 := derived1047 a h
  have h15 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1222, some c1224, some c1211, some c145, some c37, some c182, some c112, some c1216, some c194, some c98, some c15, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 57) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c1222, c1224, c1211, c145, c37, c182, c112, c1216, c194, c98, c15] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c1222 := derived1222 a h
  have h1 : Entails.eval a c1224 := derived1224 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1216 := derived1216 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1304, some c1301, some c1211, some c1306, some c389, some c388, some c1307, some c328, some c42, some c314, some c112, some c326, some c102, some c41, some c110, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 57) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c1304, c1301, c1211, c1306, c389, c388, c1307, c328, c42, c314, c112, c326, c102, c41, c110] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c1304 := derived1304 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1306 := derived1306 a h
  have h4 : Entails.eval a c389 := h 388 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c1307 := derived1307 a h
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c314 := h 313 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c1308, some c1223, some c383, some c1222, some c1304, some c1301, some c112, some c37, some c490, some c304, some c1052, some c43, some c227, some c108, some c292, some c290, some c64, some c335, some c345, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 57) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c1224, c1308, c1223, c383, c1222, c1304, c1301, c112, c37, c490, c304, c1052, c43, c227, c108, c292, c290, c64, c335, c345] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c1308 := derived1308 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c1222 := derived1222 a h
  have h5 : Entails.eval a c1304 := derived1304 a h
  have h6 : Entails.eval a c1301 := derived1301 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c490 := derived490 a h
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c1052 := derived1052 a h
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c227 := h 226 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c290 := h 289 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c335 := h 334 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨43, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨1, by decide⟩, true), (⟨45, by decide⟩, false), (⟨48, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c82, some c55, some c377, some c287, some c1052, some c227, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 57) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c42, c82, c55, c377, c287, c1052, c227] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c1052 := derived1052 a h
  have h6 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1311 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1301, some c1224, some c1308, some c1223, some c383, some c1310, some c112, some c1309, some c37, some c96, some c304, some c108, some c43, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1311 : lratChecker f1311 p1311 = .success := by decide +kernel
theorem unsat1311 : Unsatisfiable (PosFin 57) f1311 := by
  apply lratCheckerSound f1311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1311
  · intro a ha; simp [p1311] at ha; subst a; trivial
  · exact checked1311
theorem derived1311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1311 := by
  apply localUnsat_implies_entails f1311 [c1301, c1224, c1308, c1223, c383, c1310, c112, c1309, c37, c96, c304, c108, c43] c1311 unsat1311 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1224 := derived1224 a h
  have h2 : Entails.eval a c1308 := derived1308 a h
  have h3 : Entails.eval a c1223 := derived1223 a h
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c1310 := derived1310 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1309 := derived1309 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1312 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1311, some c1304, some c1224, some c306, some c79, some c59, some c1303, some c351, some c292, some c1218, some c1277, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1312 : lratChecker f1312 p1312 = .success := by decide +kernel
theorem unsat1312 : Unsatisfiable (PosFin 57) f1312 := by
  apply lratCheckerSound f1312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1312
  · intro a ha; simp [p1312] at ha; subst a; trivial
  · exact checked1312
theorem derived1312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1312 := by
  apply localUnsat_implies_entails f1312 [c1311, c1304, c1224, c306, c79, c59, c1303, c351, c292, c1218, c1277] c1312 unsat1312 (by rfl) a
  have h0 : Entails.eval a c1311 := derived1311 a h
  have h1 : Entails.eval a c1304 := derived1304 a h
  have h2 : Entails.eval a c1224 := derived1224 a h
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c1218 := derived1218 a h
  have h10 : Entails.eval a c1277 := derived1277 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1313 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1301, some c1224, some c1287, some c145, some c37, some c312, some c10, some c111, some c326, some c43, some c318, some c324, some c150, some c115, some c173, some c26, some c218, some c254, some c83, some c298, some c74, some c241, some c21, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1313 : lratChecker f1313 p1313 = .success := by decide +kernel
theorem unsat1313 : Unsatisfiable (PosFin 57) f1313 := by
  apply lratCheckerSound f1313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1313
  · intro a ha; simp [p1313] at ha; subst a; trivial
  · exact checked1313
theorem derived1313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1313 := by
  apply localUnsat_implies_entails f1313 [c1301, c1224, c1287, c145, c37, c312, c10, c111, c326, c43, c318, c324, c150, c115, c173, c26, c218, c254, c83, c298, c74, c241, c21] c1313 unsat1313 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1224 := derived1224 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c218 := h 217 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c83 := h 82 (by decide)
  have h19 : Entails.eval a c298 := h 297 (by decide)
  have h20 : Entails.eval a c74 := h 73 (by decide)
  have h21 : Entails.eval a c241 := h 240 (by decide)
  have h22 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1314 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1311, some c1304, some c1224, some c1211, some c1313, some c306, some c328, some c1312, some c59, some c143, some c1222, some c292, some c290, some c182, some c171, some c192, some c8, some c177, some c85, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 57) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c1311, c1304, c1224, c1211, c1313, c306, c328, c1312, c59, c143, c1222, c292, c290, c182, c171, c192, c8, c177, c85] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c1311 := derived1311 a h
  have h1 : Entails.eval a c1304 := derived1304 a h
  have h2 : Entails.eval a c1224 := derived1224 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c1313 := derived1313 a h
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c1312 := derived1312 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c1222 := derived1222 a h
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c192 := h 191 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c177 := h 176 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1304, some c1301, some c1314, some c42, some c328, some c145, some c37, some c312, some c326, some c324, some c318, some c43, some c12, some c116, some c144, some c28, some c1047, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 57) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c1304, c1301, c1314, c42, c328, c145, c37, c312, c326, c324, c318, c43, c12, c116, c144, c28, c1047] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c1304 := derived1304 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1314 := derived1314 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c144 := h 143 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c1047 := derived1047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c145, some c43, some c12, some c116, some c144, some c28, some c258, some c389, some c212, some c318, some c326, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 57) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c37, c145, c43, c12, c116, c144, c28, c258, c389, c212, c318, c326] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c78, some c98, some c305, some c388, some c1223, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 57) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c318, c78, c98, c305, c388, c1223] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c1223 := derived1223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1315, some c1311, some c1304, some c1301, some c1224, some c1211, some c42, some c328, some c1316, some c324, some c41, some c110, some c1317, some c389, some c1223, some c383, some c1222, some c82, some c1059, some c377, some c79, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 57) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c1315, c1311, c1304, c1301, c1224, c1211, c42, c328, c1316, c324, c41, c110, c1317, c389, c1223, c383, c1222, c82, c1059, c377, c79] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c1315 := derived1315 a h
  have h1 : Entails.eval a c1311 := derived1311 a h
  have h2 : Entails.eval a c1304 := derived1304 a h
  have h3 : Entails.eval a c1301 := derived1301 a h
  have h4 : Entails.eval a c1224 := derived1224 a h
  have h5 : Entails.eval a c1211 := derived1211 a h
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c1316 := derived1316 a h
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c1317 := derived1317 a h
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c1223 := derived1223 a h
  have h15 : Entails.eval a c383 := h 382 (by decide)
  have h16 : Entails.eval a c1222 := derived1222 a h
  have h17 : Entails.eval a c82 := h 81 (by decide)
  have h18 : Entails.eval a c1059 := derived1059 a h
  have h19 : Entails.eval a c377 := h 376 (by decide)
  have h20 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1218, some c1216, some c391, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c1218, c1216, c391] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c1218 := derived1218 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c255, some c254, some c140, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c255, c254, c140] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c254 := h 253 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, true), (⟨41, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c388, some c198, some c365, some c1320, some c221, some c342, some c343, some c172, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c391, c388, c198, c365, c1320, c221, c342, c343, c172] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c365 := h 364 (by decide)
  have h4 : Entails.eval a c1320 := derived1320 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c343 := h 342 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1210, some c1211, some c1086, some c108, some c1213, some c5, some c1319, some c203, some c176, some c180, some c1321, some c194, some c143, some c389, some c365, some c385, some c145, some c328, some c327, some c48, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c1210, c1211, c1086, c108, c1213, c5, c1319, c203, c176, c180, c1321, c194, c143, c389, c365, c385, c145, c328, c327, c48] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c1210 := derived1210 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1086 := derived1086 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1213 := derived1213 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c1319 := derived1319 a h
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c1321 := derived1321 a h
  have h11 : Entails.eval a c194 := h 193 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c365 := h 364 (by decide)
  have h15 : Entails.eval a c385 := h 384 (by decide)
  have h16 : Entails.eval a c145 := h 144 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c327 := h 326 (by decide)
  have h19 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c388, some c192, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c391, c388, c192] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c192, some c389, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c198, c192, c389] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c1210, some c105, some c1211, some c1086, some c108, some c1213, some c1, some c2, some c1322, some c1324, some c385, some c1287, some c322, some c1122, some c1226, some c1124, some c59, some c354, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c106, c1210, c105, c1211, c1086, c108, c1213, c1, c2, c1322, c1324, c385, c1287, c322, c1122, c1226, c1124, c59, c354] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c1086 := derived1086 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1213 := derived1213 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1322 := derived1322 a h
  have h10 : Entails.eval a c1324 := derived1324 a h
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c1287 := derived1287 a h
  have h13 : Entails.eval a c322 := h 321 (by decide)
  have h14 : Entails.eval a c1122 := derived1122 a h
  have h15 : Entails.eval a c1226 := derived1226 a h
  have h16 : Entails.eval a c1124 := derived1124 a h
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c327, some c48, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c328, c327, c48] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c154, some c322, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c150, c154, c322] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1210, some c322, some c326, some c307, some c1189, some c312, some c194, some c388, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c1211, c1210, c322, c326, c307, c1189, c312, c194, c388] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c322 := h 321 (by decide)
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c1189 := derived1189 a h
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c106, some c1211, some c1210, some c1328, some c318, some c118, some c389, some c18, some c312, some c113, some c121, some c300, some c280, some c508, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c7, c106, c1211, c1210, c1328, c318, c118, c389, c18, c312, c113, c121, c300, c280, c508] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1210 := derived1210 a h
  have h4 : Entails.eval a c1328 := derived1328 a h
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c312 := h 311 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  have h14 : Entails.eval a c508 := derived508 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c1210, some c1211, some c1086, some c108, some c1213, some c5, some c7, some c1327, some c1326, some c1329, some c385, some c391, some c190, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c106, c1210, c1211, c1086, c108, c1213, c5, c7, c1327, c1326, c1329, c385, c391, c190] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1086 := derived1086 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1213 := derived1213 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c1327 := derived1327 a h
  have h9 : Entails.eval a c1326 := derived1326 a h
  have h10 : Entails.eval a c1329 := derived1329 a h
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c391 := h 390 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c23, some c129, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c18, c23, c129] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c326, some c149, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c322, c326, c149] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c326 := h 325 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨55, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c143, some c150, some c115, some c263, some c323, some c220, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c143, c150, c115, c263, c323, c220] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨55, by decide⟩, false), (⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1333, some c1326, some c218, some c17, some c26, some c130, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c105, c1333, c1326, c218, c17, c26, c130] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1333 := derived1333 a h
  have h2 : Entails.eval a c1326 := derived1326 a h
  have h3 : Entails.eval a c218 := h 217 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1323, some c145, some c192, some c1326, some c389, some c314, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c1323, c145, c192, c1326, c389, c314] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c1323 := derived1323 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c1326 := derived1326 a h
  have h4 : Entails.eval a c389 := h 388 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c108, some c106, some c1210, some c1211, some c1213, some c1086, some c1325, some c1330, some c1331, some c1332, some c1334, some c10, some c1335, some c385, some c1287, some c189, some c323, some c296, some c1023, some c389, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c105, c108, c106, c1210, c1211, c1213, c1086, c1325, c1330, c1331, c1332, c1334, c10, c1335, c385, c1287, c189, c323, c296, c1023, c389] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1210 := derived1210 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c1213 := derived1213 a h
  have h6 : Entails.eval a c1086 := derived1086 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c1330 := derived1330 a h
  have h9 : Entails.eval a c1331 := derived1331 a h
  have h10 : Entails.eval a c1332 := derived1332 a h
  have h11 : Entails.eval a c1334 := derived1334 a h
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c1335 := derived1335 a h
  have h14 : Entails.eval a c385 := h 384 (by decide)
  have h15 : Entails.eval a c1287 := derived1287 a h
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c323 := h 322 (by decide)
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c1023 := derived1023 a h
  have h20 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c108, some c1213, some c1322, some c1319, some c202, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c5, c108, c1213, c1322, c1319, c202] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1213 := derived1213 a h
  have h3 : Entails.eval a c1322 := derived1322 a h
  have h4 : Entails.eval a c1319 := derived1319 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c5, some c1337, some c4, some c1218, some c1216, some c1319, some c392, some c100, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c108, c5, c1337, c4, c1218, c1216, c1319, c392, c100] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c1337 := derived1337 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c1218 := derived1218 a h
  have h5 : Entails.eval a c1216 := derived1216 a h
  have h6 : Entails.eval a c1319 := derived1319 a h
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1218, some c202, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c1324, c1218, c202] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1218 := derived1218 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c323, some c52, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c322, c323, c52] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨32, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1213, some c1086, some c1339, some c385, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c1211, c1213, c1086, c1339, c385] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c1086 := derived1086 a h
  have h3 : Entails.eval a c1339 := derived1339 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1336, some c105, some c108, some c1235, some c1, some c1338, some c1340, some c1287, some c1341, some c4, some c1218, some c385, some c783, some c1086, some c79, some c100, some c389, some c1323, some c1319, some c193, some c1222, some c183, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c1336, c105, c108, c1235, c1, c1338, c1340, c1287, c1341, c4, c1218, c385, c783, c1086, c79, c100, c389, c1323, c1319, c193, c1222, c183] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c1336 := derived1336 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1235 := derived1235 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1338 := derived1338 a h
  have h6 : Entails.eval a c1340 := derived1340 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c1341 := derived1341 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c1218 := derived1218 a h
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c783 := derived783 a h
  have h13 : Entails.eval a c1086 := derived1086 a h
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c100 := h 99 (by decide)
  have h16 : Entails.eval a c389 := h 388 (by decide)
  have h17 : Entails.eval a c1323 := derived1323 a h
  have h18 : Entails.eval a c1319 := derived1319 a h
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c1222 := derived1222 a h
  have h21 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1328, some c38, some c118, some c254, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c1328, c38, c118, c254] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1210, some c1211, some c1213, some c1340, some c1086, some c1287, some c113, some c150, some c385, some c1326, some c1343, some c206, some c205, some c1216, some c151, some c388, some c324, some c312, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1210, c1211, c1213, c1340, c1086, c1287, c113, c150, c385, c1326, c1343, c206, c205, c1216, c151, c388, c324, c312] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1210 := derived1210 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1213 := derived1213 a h
  have h3 : Entails.eval a c1340 := derived1340 a h
  have h4 : Entails.eval a c1086 := derived1086 a h
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c385 := h 384 (by decide)
  have h9 : Entails.eval a c1326 := derived1326 a h
  have h10 : Entails.eval a c1343 := derived1343 a h
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c1216 := derived1216 a h
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c388 := h 387 (by decide)
  have h16 : Entails.eval a c324 := h 323 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1342, some c1336, some c105, some c108, some c5, some c1344, some c8, some c1215, some c1340, some c1287, some c113, some c150, some c20, some c17, some c1326, some c135, some c21, some c212, some c326, some c38, some c218, some c254, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c1342, c1336, c105, c108, c5, c1344, c8, c1215, c1340, c1287, c113, c150, c20, c17, c1326, c135, c21, c212, c326, c38, c218, c254] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c1342 := derived1342 a h
  have h1 : Entails.eval a c1336 := derived1336 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1344 := derived1344 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1340 := derived1340 a h
  have h9 : Entails.eval a c1287 := derived1287 a h
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c150 := h 149 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c1326 := derived1326 a h
  have h15 : Entails.eval a c135 := h 134 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c212 := h 211 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c38 := h 37 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1210, some c1211, some c1213, some c1340, some c1332, some c1086, some c1287, some c113, some c38, some c385, some c254, some c1335, some c1334, some c10, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c105, c1210, c1211, c1213, c1340, c1332, c1086, c1287, c113, c38, c385, c254, c1335, c1334, c10] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1213 := derived1213 a h
  have h4 : Entails.eval a c1340 := derived1340 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1086 := derived1086 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c254 := h 253 (by decide)
  have h12 : Entails.eval a c1335 := derived1335 a h
  have h13 : Entails.eval a c1334 := derived1334 a h
  have h14 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1340, some c1332, some c1287, some c113, some c1301, some c52, some c38, some c20, some c1086, some c308, some c254, some c255, some c92, some c118, some c1100, some c771, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c1340, c1332, c1287, c113, c1301, c52, c38, c20, c1086, c308, c254, c255, c92, c118, c1100, c771] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c1301 := derived1301 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c1086 := derived1086 a h
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c1100 := derived1100 a h
  have h15 : Entails.eval a c771 := derived771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1326, some c150, some c115, some c321, some c21, some c52, some c48, some c114, some c325, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c108, c1326, c150, c115, c321, c21, c52, c48, c114, c325] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1326 := derived1326 a h
  have h2 : Entails.eval a c150 := h 149 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c1151, some c305, some c153, some c92, some c188, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c52, c1151, c305, c153, c92, c188] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c1151 := derived1151 a h
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1336, some c1342, some c1345, some c1346, some c105, some c1347, some c1215, some c1221, some c1326, some c1219, some c1348, some c10, some c1323, some c1220, some c76, some c304, some c1224, some c1349, some c321, some c113, some c20, some c17, some c215, some c132, some c21, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c108, c1336, c1342, c1345, c1346, c105, c1347, c1215, c1221, c1326, c1219, c1348, c10, c1323, c1220, c76, c304, c1224, c1349, c321, c113, c20, c17, c215, c132, c21] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1336 := derived1336 a h
  have h2 : Entails.eval a c1342 := derived1342 a h
  have h3 : Entails.eval a c1345 := derived1345 a h
  have h4 : Entails.eval a c1346 := derived1346 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1347 := derived1347 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1221 := derived1221 a h
  have h9 : Entails.eval a c1326 := derived1326 a h
  have h10 : Entails.eval a c1219 := derived1219 a h
  have h11 : Entails.eval a c1348 := derived1348 a h
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c1323 := derived1323 a h
  have h14 : Entails.eval a c1220 := derived1220 a h
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c1224 := derived1224 a h
  have h18 : Entails.eval a c1349 := derived1349 a h
  have h19 : Entails.eval a c321 := h 320 (by decide)
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c20 := h 19 (by decide)
  have h22 : Entails.eval a c17 := h 16 (by decide)
  have h23 : Entails.eval a c215 := h 214 (by decide)
  have h24 : Entails.eval a c132 := h 131 (by decide)
  have h25 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1340, some c1332, some c1287, some c113, some c1118, some c52, some c38, some c385, some c20, some c254, some c1086, some c79, some c218, some c251, some c306, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1340, c1332, c1287, c113, c1118, c52, c38, c385, c20, c254, c1086, c79, c218, c251, c306] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c1118 := derived1118 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c1086 := derived1086 a h
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c218 := h 217 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1215, some c391, some c1219, some c190, some c385, some c783, some c79, some c39, some c389, some c303, some c193, some c1222, some c188, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c1215, c391, c1219, c190, c385, c783, c79, c39, c389, c303, c193, c1222, c188] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c1215 := derived1215 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c1219 := derived1219 a h
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c783 := derived783 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c1222 := derived1222 a h
  have h12 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1352, some c100, some c385, some c392, some c190, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1352, c100, c385, c392, c190] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1352 := derived1352 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c392 := h 391 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c391, some c1219, some c1326, some c117, some c152, some c264, some c17, some c324, some c129, some c217, some c24, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c105, c391, c1219, c1326, c117, c152, c264, c17, c324, c129, c217, c24] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c1219 := derived1219 a h
  have h3 : Entails.eval a c1326 := derived1326 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c105, some c1336, some c1342, some c1345, some c1346, some c1350, some c1351, some c1353, some c10, some c1354, some c1220, some c100, some c392, some c1219, some c1326, some c324, some c152, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 57) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c108, c105, c1336, c1342, c1345, c1346, c1350, c1351, c1353, c10, c1354, c1220, c100, c392, c1219, c1326, c324, c152] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1336 := derived1336 a h
  have h3 : Entails.eval a c1342 := derived1342 a h
  have h4 : Entails.eval a c1345 := derived1345 a h
  have h5 : Entails.eval a c1346 := derived1346 a h
  have h6 : Entails.eval a c1350 := derived1350 a h
  have h7 : Entails.eval a c1351 := derived1351 a h
  have h8 : Entails.eval a c1353 := derived1353 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c1354 := derived1354 a h
  have h11 : Entails.eval a c1220 := derived1220 a h
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c392 := h 391 (by decide)
  have h14 : Entails.eval a c1219 := derived1219 a h
  have h15 : Entails.eval a c1326 := derived1326 a h
  have h16 : Entails.eval a c324 := h 323 (by decide)
  have h17 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1235, some c5, some c1355, some c108, some c106, some c7, some c1211, some c1214, some c1213, some c1086, some c391, some c385, some c1216, some c194, some c176, some c180, some c389, some c365, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 57) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c1235, c5, c1355, c108, c106, c7, c1211, c1214, c1213, c1086, c391, c385, c1216, c194, c176, c180, c389, c365] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c1355 := derived1355 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c1211 := derived1211 a h
  have h7 : Entails.eval a c1214 := derived1214 a h
  have h8 : Entails.eval a c1213 := derived1213 a h
  have h9 : Entails.eval a c1086 := derived1086 a h
  have h10 : Entails.eval a c391 := h 390 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c1216 := derived1216 a h
  have h13 : Entails.eval a c194 := h 193 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c389 := h 388 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1214, some c1086, some c385, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 57) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c1211, c1214, c1086, c385] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1214 := derived1214 a h
  have h2 : Entails.eval a c1086 := derived1086 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1235, some c1340, some c1287, some c1357, some c4, some c1216, some c201, some c77, some c1278, some c102, some c1301, some c1060, some c1288, some c1236, some c343, some c351, some c384, some c330, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 57) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c1235, c1340, c1287, c1357, c4, c1216, c201, c77, c1278, c102, c1301, c1060, c1288, c1236, c343, c351, c384, c330] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1340 := derived1340 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c1357 := derived1357 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1216 := derived1216 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c1278 := derived1278 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c1301 := derived1301 a h
  have h11 : Entails.eval a c1060 := derived1060 a h
  have h12 : Entails.eval a c1288 := derived1288 a h
  have h13 : Entails.eval a c1236 := derived1236 a h
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c384 := h 383 (by decide)
  have h17 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c1355, some c108, some c1235, some c1338, some c1356, some c1340, some c1287, some c1357, some c4, some c1216, some c1358, some c385, some c391, some c100, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 57) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c5, c1355, c108, c1235, c1338, c1356, c1340, c1287, c1357, c4, c1216, c1358, c385, c391, c100] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c1355 := derived1355 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c1235 := derived1235 a h
  have h4 : Entails.eval a c1338 := derived1338 a h
  have h5 : Entails.eval a c1356 := derived1356 a h
  have h6 : Entails.eval a c1340 := derived1340 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c1357 := derived1357 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c1216 := derived1216 a h
  have h11 : Entails.eval a c1358 := derived1358 a h
  have h12 : Entails.eval a c385 := h 384 (by decide)
  have h13 : Entails.eval a c391 := h 390 (by decide)
  have h14 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1355, some c108, some c5, some c1359, some c1330, some c1344, some c8, some c1215, some c1216, some c1340, some c113, some c150, some c20, some c1326, some c135, some c37, some c50, some c262, some c21, some c326, some c212, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 57) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c1355, c108, c5, c1359, c1330, c1344, c8, c1215, c1216, c1340, c113, c150, c20, c1326, c135, c37, c50, c262, c21, c326, c212] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c1355 := derived1355 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1359 := derived1359 a h
  have h4 : Entails.eval a c1330 := derived1330 a h
  have h5 : Entails.eval a c1344 := derived1344 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1216 := derived1216 a h
  have h9 : Entails.eval a c1340 := derived1340 a h
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c150 := h 149 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c1326 := derived1326 a h
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c326 := h 325 (by decide)
  have h20 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1235, some c106, some c2, some c1211, some c1213, some c1357, some c1287, some c322, some c323, some c296, some c539, some c118, some c48, some c389, some c18, some c265, some c142, some c365, some c243, some c298, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 57) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c1235, c106, c2, c1211, c1213, c1357, c1287, c322, c323, c296, c539, c118, c48, c389, c18, c265, c142, c365, c243, c298] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c1213 := derived1213 a h
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c322 := h 321 (by decide)
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c539 := derived539 a h
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c243 := h 242 (by decide)
  have h19 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c1235, some c1340, some c1301, some c1218, some c1236, some c201, some c308, some c52, some c153, some c326, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 57) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c4, c1235, c1340, c1301, c1218, c1236, c201, c308, c52, c153, c326] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1301 := derived1301 a h
  have h4 : Entails.eval a c1218 := derived1218 a h
  have h5 : Entails.eval a c1236 := derived1236 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c308 := h 307 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1235, some c1361, some c1340, some c1287, some c1357, some c4, some c1362, some c385, some c783, some c1086, some c79, some c100, some c391, some c389, some c1216, some c1222, some c193, some c183, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 57) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1235, c1361, c1340, c1287, c1357, c4, c1362, c385, c783, c1086, c79, c100, c391, c389, c1216, c1222, c193, c183] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1361 := derived1361 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c1362 := derived1362 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c783 := derived783 a h
  have h9 : Entails.eval a c1086 := derived1086 a h
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c391 := h 390 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c1216 := derived1216 a h
  have h15 : Entails.eval a c1222 := derived1222 a h
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1210, some c1211, some c1213, some c1357, some c1287, some c189, some c323, some c296, some c389, some c1023, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 57) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c1210, c1211, c1213, c1357, c1287, c189, c323, c296, c389, c1023] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c1210 := derived1210 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1213 := derived1213 a h
  have h3 : Entails.eval a c1357 := derived1357 a h
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c1023 := derived1023 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1347, some c1351, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 57) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c1347, c1351] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c1347 := derived1347 a h
  have h1 : Entails.eval a c1351 := derived1351 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1366 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c48, some c325, some c304, some c142, some c76, some c1299, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 57) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c52, c48, c325, c304, c142, c76, c1299] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c304 := h 303 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c1299 := derived1299 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c37, some c1326, some c1219, some c1366, some c321, some c1304, some c490, some c1287, some c79, some c59, some c92, some c88, some c343, some c351, some c378, some c383, some c330, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 57) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c77, c37, c1326, c1219, c1366, c321, c1304, c490, c1287, c79, c59, c92, c88, c343, c351, c378, c383, c330] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c1326 := derived1326 a h
  have h3 : Entails.eval a c1219 := derived1219 a h
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1304 := derived1304 a h
  have h7 : Entails.eval a c490 := derived490 a h
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c343 := h 342 (by decide)
  have h14 : Entails.eval a c351 := h 350 (by decide)
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c383 := h 382 (by decide)
  have h17 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨27, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c79, some c39, some c389, some c303, some c193, some c1222, some c188, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 57) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c783, c79, c39, c389, c303, c193, c1222, c188] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c1222 := derived1222 a h
  have h7 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1363, some c1364, some c106, some c1365, some c1367, some c1215, some c391, some c1219, some c1326, some c50, some c1368, some c385, some c189, some c389, some c649, some c78, some c294, some c1023, some c303, some c59, some c88, some c354, some c383, some c57, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 57) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c1363, c1364, c106, c1365, c1367, c1215, c391, c1219, c1326, c50, c1368, c385, c189, c389, c649, c78, c294, c1023, c303, c59, c88, c354, c383, c57] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c1363 := derived1363 a h
  have h1 : Entails.eval a c1364 := derived1364 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1365 := derived1365 a h
  have h4 : Entails.eval a c1367 := derived1367 a h
  have h5 : Entails.eval a c1215 := derived1215 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c1219 := derived1219 a h
  have h8 : Entails.eval a c1326 := derived1326 a h
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c1368 := derived1368 a h
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c189 := h 188 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c649 := derived649 a h
  have h15 : Entails.eval a c78 := h 77 (by decide)
  have h16 : Entails.eval a c294 := h 293 (by decide)
  have h17 : Entails.eval a c1023 := derived1023 a h
  have h18 : Entails.eval a c303 := h 302 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c354 := h 353 (by decide)
  have h22 : Entails.eval a c383 := h 382 (by decide)
  have h23 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1220, some c100, some c385, some c392, some c191, some c1219, some c207, some c1326, some c324, some c152, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 57) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c1220, c100, c385, c392, c191, c1219, c207, c1326, c324, c152] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c1220 := derived1220 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c392 := h 391 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c1219 := derived1219 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c1326 := derived1326 a h
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1363, some c1364, some c106, some c1365, some c1215, some c1367, some c1353, some c1370, some c391, some c1369, some c1219, some c1287, some c1368, some c385, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 57) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c1363, c1364, c106, c1365, c1215, c1367, c1353, c1370, c391, c1369, c1219, c1287, c1368, c385] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c1363 := derived1363 a h
  have h1 : Entails.eval a c1364 := derived1364 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1365 := derived1365 a h
  have h4 : Entails.eval a c1215 := derived1215 a h
  have h5 : Entails.eval a c1367 := derived1367 a h
  have h6 : Entails.eval a c1353 := derived1353 a h
  have h7 : Entails.eval a c1370 := derived1370 a h
  have h8 : Entails.eval a c391 := h 390 (by decide)
  have h9 : Entails.eval a c1369 := derived1369 a h
  have h10 : Entails.eval a c1219 := derived1219 a h
  have h11 : Entails.eval a c1287 := derived1287 a h
  have h12 : Entails.eval a c1368 := derived1368 a h
  have h13 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1355, some c108, some c1360, some c1371, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 57) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c1355, c108, c1360, c1371] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c1355 := derived1355 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1360 := derived1360 a h
  have h3 : Entails.eval a c1371 := derived1371 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c1211, some c1210, some c3, some c176, some c365, some c385, some c369, some c147, some c308, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 57) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c107, c1211, c1210, c3, c176, c365, c385, c369, c147, c308] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1210 := derived1210 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1355, some c1372, some c107, some c1214, some c108, some c1213, some c391, some c1211, some c1210, some c5, some c1216, some c180, some c206, some c194, some c389, some c1373, some c190, some c385, some c369, some c188, some c308, some c147, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 57) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c1355, c1372, c107, c1214, c108, c1213, c391, c1211, c1210, c5, c1216, c180, c206, c194, c389, c1373, c190, c385, c369, c188, c308, c147] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c1355 := derived1355 a h
  have h1 : Entails.eval a c1372 := derived1372 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1214 := derived1214 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1213 := derived1213 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c1211 := derived1211 a h
  have h8 : Entails.eval a c1210 := derived1210 a h
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c1216 := derived1216 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c194 := h 193 (by decide)
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c1373 := derived1373 a h
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c385 := h 384 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c188 := h 187 (by decide)
  have h20 : Entails.eval a c308 := h 307 (by decide)
  have h21 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c193, some c389, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 57) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c200, c193, c389] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1375, some c385, some c1287, some c322, some c323, some c160, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 57) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c1375, c385, c1287, c322, c323, c160] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1210, some c539, some c78, some c307, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 57) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c1211, c1210, c539, c78, c307] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c1211, some c1210, some c3, some c1376, some c2, some c1377, some c389, some c142, some c193, some c300, some c385, some c1287, some c365, some c296, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 57) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c107, c1211, c1210, c3, c1376, c2, c1377, c389, c142, c193, c300, c385, c1287, c365, c296] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1210 := derived1210 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1376 := derived1376 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c1377 := derived1377 a h
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c300 := h 299 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c1287 := derived1287 a h
  have h13 : Entails.eval a c365 := h 364 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1287, some c189, some c323, some c296, some c389, some c1023, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 57) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c1287, c189, c323, c296, c389, c1023] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c1287 := derived1287 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c389 := h 388 (by decide)
  have h5 : Entails.eval a c1023 := derived1023 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨22, by decide⟩, true), (⟨55, by decide⟩, true), (⟨30, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c220, some c11, some c19, some c27, some c130, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 57) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c147, c220, c11, c19, c27, c130] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c220 := h 219 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨55, by decide⟩, true), (⟨30, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c1211, some c1210, some c1380, some c323, some c308, some c113, some c1118, some c19, some c218, some c1100, some c227, some c1074, some c290, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 57) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c107, c1211, c1210, c1380, c323, c308, c113, c1118, c19, c218, c1100, c227, c1074, c290] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1210 := derived1210 a h
  have h3 : Entails.eval a c1380 := derived1380 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c1118 := derived1118 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c218 := h 217 (by decide)
  have h10 : Entails.eval a c1100 := derived1100 a h
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c1074 := derived1074 a h
  have h13 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1355, some c1372, some c107, some c1210, some c1211, some c1214, some c1213, some c1374, some c1378, some c1332, some c1379, some c385, some c1381, some c1331, some c38, some c389, some c254, some c193, some c129, some c11, some c21, some c130, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 57) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c108, c1355, c1372, c107, c1210, c1211, c1214, c1213, c1374, c1378, c1332, c1379, c385, c1381, c1331, c38, c389, c254, c193, c129, c11, c21, c130] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1355 := derived1355 a h
  have h2 : Entails.eval a c1372 := derived1372 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1210 := derived1210 a h
  have h5 : Entails.eval a c1211 := derived1211 a h
  have h6 : Entails.eval a c1214 := derived1214 a h
  have h7 : Entails.eval a c1213 := derived1213 a h
  have h8 : Entails.eval a c1374 := derived1374 a h
  have h9 : Entails.eval a c1378 := derived1378 a h
  have h10 : Entails.eval a c1332 := derived1332 a h
  have h11 : Entails.eval a c1379 := derived1379 a h
  have h12 : Entails.eval a c385 := h 384 (by decide)
  have h13 : Entails.eval a c1381 := derived1381 a h
  have h14 : Entails.eval a c1331 := derived1331 a h
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c389 := h 388 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  have h19 : Entails.eval a c129 := h 128 (by decide)
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1235, some c1382, some c1211, some c1212, some c1086, some c392, some c1218, some c145, some c180, some c206, some c176, some c203, some c198, some c1321, some c1213, some c109, some c6, some c1340, some c144, some c1287, some c1185, some c327, some c46, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 57) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1235, c1382, c1211, c1212, c1086, c392, c1218, c145, c180, c206, c176, c203, c198, c1321, c1213, c109, c6, c1340, c144, c1287, c1185, c327, c46] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1382 := derived1382 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1212 := derived1212 a h
  have h4 : Entails.eval a c1086 := derived1086 a h
  have h5 : Entails.eval a c392 := h 391 (by decide)
  have h6 : Entails.eval a c1218 := derived1218 a h
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c198 := h 197 (by decide)
  have h13 : Entails.eval a c1321 := derived1321 a h
  have h14 : Entails.eval a c1213 := derived1213 a h
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c1340 := derived1340 a h
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c1287 := derived1287 a h
  have h20 : Entails.eval a c1185 := derived1185 a h
  have h21 : Entails.eval a c327 := h 326 (by decide)
  have h22 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨31, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c35, some c303, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 57) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c75, c35, c303] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1235, some c1382, some c1383, some c106, some c4, some c1340, some c1218, some c1287, some c385, some c79, some c39, some c1384, some c391, some c100, some c1217, some c6, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 57) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c1235, c1382, c1383, c106, c4, c1340, c1218, c1287, c385, c79, c39, c1384, c391, c100, c1217, c6] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1382 := derived1382 a h
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1340 := derived1340 a h
  have h6 : Entails.eval a c1218 := derived1218 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c385 := h 384 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c1384 := derived1384 a h
  have h12 : Entails.eval a c391 := h 390 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c1217 := derived1217 a h
  have h15 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c1, some c1235, some c1214, some c77, some c1278, some c106, some c173, some c1340, some c102, some c1358, some c1287, some c1288, some c182, some c75, some c55, some c351, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 57) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c201, c1, c1235, c1214, c77, c1278, c106, c173, c1340, c102, c1358, c1287, c1288, c182, c75, c55, c351] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1235 := derived1235 a h
  have h3 : Entails.eval a c1214 := derived1214 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c1278 := derived1278 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  have h8 : Entails.eval a c1340 := derived1340 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c1358 := derived1358 a h
  have h11 : Entails.eval a c1287 := derived1287 a h
  have h12 : Entails.eval a c1288 := derived1288 a h
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c55 := h 54 (by decide)
  have h16 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1212, some c1086, some c392, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 57) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c1211, c1212, c1086, c392] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1212 := derived1212 a h
  have h2 : Entails.eval a c1086 := derived1086 a h
  have h3 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1382, some c1235, some c1385, some c1386, some c1387, some c106, some c4, some c1340, some c1287, some c385, some c79, some c39, some c1384, some c391, some c100, some c1217, some c6, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 57) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c1382, c1235, c1385, c1386, c1387, c106, c4, c1340, c1287, c385, c79, c39, c1384, c391, c100, c1217, c6] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c1382 := derived1382 a h
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c1385 := derived1385 a h
  have h3 : Entails.eval a c1386 := derived1386 a h
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c1340 := derived1340 a h
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c1384 := derived1384 a h
  have h13 : Entails.eval a c391 := h 390 (by decide)
  have h14 : Entails.eval a c100 := h 99 (by decide)
  have h15 : Entails.eval a c1217 := derived1217 a h
  have h16 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1213, some c1210, some c1211, some c1086, some c1212, some c322, some c323, some c296, some c1004, some c1007, some c280, some c68, some c67, some c349, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 57) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c1213, c1210, c1211, c1086, c1212, c322, c323, c296, c1004, c1007, c280, c68, c67, c349] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c1213 := derived1213 a h
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1086 := derived1086 a h
  have h4 : Entails.eval a c1212 := derived1212 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c1004 := derived1004 a h
  have h9 : Entails.eval a c1007 := derived1007 a h
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1213, some c1212, some c69, some c67, some c349, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 57) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c1213, c1212, c69, c67, c349] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c1213 := derived1213 a h
  have h1 : Entails.eval a c1212 := derived1212 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1391 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨40, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1210, some c118, some c1099, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 57) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c1211, c1210, c118, c1099] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c1099 := derived1099 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1210, some c1382, some c109, some c7, some c1390, some c1391, some c18, some c113, some c121, some c280, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 57) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c1210, c1382, c109, c7, c1390, c1391, c18, c113, c121, c280] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c1210 := derived1210 a h
  have h1 : Entails.eval a c1382 := derived1382 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1390 := derived1390 a h
  have h5 : Entails.eval a c1391 := derived1391 a h
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1392

end CochromaticTwenty.Certificates.B16_6_2
