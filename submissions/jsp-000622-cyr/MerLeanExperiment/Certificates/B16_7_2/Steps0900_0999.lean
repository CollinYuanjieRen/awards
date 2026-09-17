import MerLeanExperiment.Certificates.B16_7_2.Steps0800_0899

/-! Generated from the actual pinned b16_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1289 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨29, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c344, some c57, some c368, some c80, some c370, some c39, some c1288, some c98, some c51, some c81, some c300, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 57) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c37, c344, c57, c368, c80, c370, c39, c1288, c98, c51, c81, c300] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c370 := h 369 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c1288 := derived1288 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c82, some c369, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 57) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c96, c82, c369] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1291 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c1289, some c68, some c56, some c368, some c57, some c346, some c39, some c1290, some c98, some c51, some c69, some c284, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 57) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c37, c1289, c68, c56, c368, c57, c346, c39, c1290, c98, c51, c69, c284] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c1289 := derived1289 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c346 := h 345 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c1290 := derived1290 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨36, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c345, some c72, some c70, some c282, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 57) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c94, c345, c72, c70, c282] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1293 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c71, some c298, some c284, some c59, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 57) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c57, c71, c298, c284, c59] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1293, some c282, some c59, some c298, some c300, some c83, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 57) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c1293, c282, c59, c298, c300, c83] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c1293 := derived1293 a h
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c49, some c1294, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 57) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c48, c49, c1294] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c1294 := derived1294 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c1292, some c68, some c56, some c282, some c369, some c57, some c84, some c298, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 57) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c94, c1292, c68, c56, c282, c369, c57, c84, c298] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c1292 := derived1292 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c1288, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 57) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c344, c1288] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c1288 := derived1288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1298 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1291, some c1287, some c48, some c320, some c1295, some c98, some c1296, some c1060, some c1297, some c56, some c368, some c1290, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 57) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c1291, c1287, c48, c320, c1295, c98, c1296, c1060, c1297, c56, c368, c1290] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c1291 := derived1291 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c1295 := derived1295 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c1296 := derived1296 a h
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c1297 := derived1297 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c1290 := derived1290 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1277, some c1282, some c1298, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 57) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c100, c1277, c1282, c1298] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1298 := derived1298 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨36, by decide⟩, false), (⟨32, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c345, some c283, some c38, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 57) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c70, c345, c283, c38] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c313, some c298, some c284, some c219, some c19, some c27, some c202, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 57) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c320, c313, c298, c284, c219, c19, c27, c202] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨33, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c11, some c113, some c182, some c245, some c18, some c19, some c230, some c212, some c283, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 57) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c3, c11, c113, c182, c245, c18, c19, c230, c212, c283] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c230 := h 229 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1303 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1302, some c801, some c139, some c19, some c258, some c422, some c113, some c117, some c165, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 57) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c1302, c801, c139, c19, c258, c422, c113, c117, c165] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c1302 := derived1302 a h
  have h1 : Entails.eval a c801 := derived801 a h
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c422 := derived422 a h
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨25, by decide⟩, true), (⟨38, by decide⟩, true), (⟨6, by decide⟩, false), (⟨37, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c715, some c105, some c245, some c18, some c230, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 57) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c3, c715, c105, c245, c18, c230] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c715 := derived715 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1303, some c350, some c351, some c272, some c1304, some c801, some c164, some c19, some c2, some c105, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 57) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1303, c350, c351, c272, c1304, c801, c164, c19, c2, c105] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1303 := derived1303 a h
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c1304 := derived1304 a h
  have h5 : Entails.eval a c801 := derived801 a h
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c99, some c344, some c57, some c71, some c1300, some c1301, some c1305, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 57) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c387, c99, c344, c57, c71, c1300, c1301, c1305] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c1300 := derived1300 a h
  have h6 : Entails.eval a c1301 := derived1301 a h
  have h7 : Entails.eval a c1305 := derived1305 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨48, by decide⟩, false), (⟨45, by decide⟩, true), (⟨44, by decide⟩, false), (⟨32, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c82, some c299, some c369, some c38, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 57) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c82, c299, c369, c38] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c313, some c284, some c300, some c219, some c19, some c27, some c202, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 57) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c320, c313, c284, c300, c219, c19, c27, c202] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨31, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c346, some c356, some c139, some c3, some c11, some c154, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 57) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c351, c346, c356, c139, c3, c11, c154] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c11, some c135, some c182, some c278, some c333, some c154, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 57) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c3, c11, c135, c182, c278, c333, c154] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c278 := h 277 (by decide)
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1311 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c105, some c269, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1311 : lratChecker f1311 p1311 = .success := by decide +kernel
theorem unsat1311 : Unsatisfiable (PosFin 57) f1311 := by
  apply lratCheckerSound f1311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1311
  · intro a ha; simp [p1311] at ha; subst a; trivial
  · exact checked1311
theorem derived1311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1311 := by
  apply localUnsat_implies_entails f1311 [c113, c105, c269] c1311 unsat1311 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1312 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c1277, some c387, some c1306, some c56, some c69, some c368, some c57, some c83, some c1307, some c1308, some c1309, some c1310, some c801, some c19, some c1311, some c2, some c164, some c152, some c283, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1312 : lratChecker f1312 p1312 = .success := by decide +kernel
theorem unsat1312 : Unsatisfiable (PosFin 57) f1312 := by
  apply lratCheckerSound f1312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1312
  · intro a ha; simp [p1312] at ha; subst a; trivial
  · exact checked1312
theorem derived1312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1312 := by
  apply localUnsat_implies_entails f1312 [c99, c1277, c387, c1306, c56, c69, c368, c57, c83, c1307, c1308, c1309, c1310, c801, c19, c1311, c2, c164, c152, c283] c1312 unsat1312 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c1306 := derived1306 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c1307 := derived1307 a h
  have h10 : Entails.eval a c1308 := derived1308 a h
  have h11 : Entails.eval a c1309 := derived1309 a h
  have h12 : Entails.eval a c1310 := derived1310 a h
  have h13 : Entails.eval a c801 := derived801 a h
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c1311 := derived1311 a h
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c152 := h 151 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1313 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨45, by decide⟩, true), (⟨32, by decide⟩, false), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c1277, some c83, some c57, some c1312, some c95, some c701, some c56, some c69, some c1307, some c1308, some c139, some c3, some c1311, some c18, some c19, some c212, some c283, some c299, some c218, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1313 : lratChecker f1313 p1313 = .success := by decide +kernel
theorem unsat1313 : Unsatisfiable (PosFin 57) f1313 := by
  apply lratCheckerSound f1313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1313
  · intro a ha; simp [p1313] at ha; subst a; trivial
  · exact checked1313
theorem derived1313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1313 := by
  apply localUnsat_implies_entails f1313 [c99, c1277, c83, c57, c1312, c95, c701, c56, c69, c1307, c1308, c139, c3, c1311, c18, c19, c212, c283, c299, c218] c1313 unsat1313 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c1312 := derived1312 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c701 := derived701 a h
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c1307 := derived1307 a h
  have h10 : Entails.eval a c1308 := derived1308 a h
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c1311 := derived1311 a h
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c212 := h 211 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c299 := h 298 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1314 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨55, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c83, some c57, some c49, some c139, some c3, some c11, some c1311, some c115, some c19, some c21, some c1013, some c205, some c236, some c292, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 57) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c1299, c99, c100, c1277, c83, c57, c49, c139, c3, c11, c1311, c115, c19, c21, c1013, c205, c236, c292] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c1311 := derived1311 a h
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c1013 := derived1013 a h
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c236 := h 235 (by decide)
  have h17 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨28, by decide⟩, true), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1277, some c1299, some c99, some c49, some c1312, some c95, some c701, some c57, some c83, some c1313, some c355, some c1314, some c320, some c313, some c300, some c282, some c219, some c19, some c27, some c202, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 57) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c100, c1277, c1299, c99, c49, c1312, c95, c701, c57, c83, c1313, c355, c1314, c320, c313, c300, c282, c219, c19, c27, c202] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1299 := derived1299 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c1312 := derived1312 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c1313 := derived1313 a h
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c1314 := derived1314 a h
  have h13 : Entails.eval a c320 := h 319 (by decide)
  have h14 : Entails.eval a c313 := h 312 (by decide)
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c282 := h 281 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c19 := h 18 (by decide)
  have h19 : Entails.eval a c27 := h 26 (by decide)
  have h20 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨31, by decide⟩, true), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c212, some c318, some c314, some c283, some c141, some c118, some c7, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 57) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c18, c212, c318, c314, c283, c141, c118, c7] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1315, some c100, some c1277, some c1299, some c99, some c49, some c1312, some c95, some c701, some c56, some c69, some c1301, some c139, some c3, some c1311, some c19, some c1316, some c94, some c347, some c369, some c58, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 57) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c1315, c100, c1277, c1299, c99, c49, c1312, c95, c701, c56, c69, c1301, c139, c3, c1311, c19, c1316, c94, c347, c369, c58] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c1315 := derived1315 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c1312 := derived1312 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c701 := derived701 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c1301 := derived1301 a h
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c1311 := derived1311 a h
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c1316 := derived1316 a h
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c347 := h 346 (by decide)
  have h19 : Entails.eval a c369 := h 368 (by decide)
  have h20 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨56, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c1299, some c139, some c3, some c11, some c1311, some c154, some c115, some c19, some c269, some c21, some c715, some c205, some c382, some c318, some c312, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 57) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c701, c1299, c139, c3, c11, c1311, c154, c115, c19, c269, c21, c715, c205, c382, c318, c312] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c1311 := derived1311 a h
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c269 := h 268 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c715 := derived715 a h
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1315, some c100, some c1277, some c1299, some c99, some c49, some c1312, some c95, some c1317, some c355, some c1318, some c320, some c313, some c298, some c282, some c219, some c19, some c27, some c202, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c1315, c100, c1277, c1299, c99, c49, c1312, c95, c1317, c355, c1318, c320, c313, c298, c282, c219, c19, c27, c202] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c1315 := derived1315 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c1312 := derived1312 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c1317 := derived1317 a h
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c1318 := derived1318 a h
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c282 := h 281 (by decide)
  have h15 : Entails.eval a c219 := h 218 (by decide)
  have h16 : Entails.eval a c19 := h 18 (by decide)
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c105, some c272, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c113, c105, c272] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c49, some c1312, some c95, some c701, some c1315, some c1319, some c71, some c1301, some c139, some c3, some c1320, some c19, some c1316, some c94, some c70, some c347, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c1299, c99, c100, c1277, c49, c1312, c95, c701, c1315, c1319, c71, c1301, c139, c3, c1320, c19, c1316, c94, c70, c347] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c1312 := derived1312 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c1315 := derived1315 a h
  have h9 : Entails.eval a c1319 := derived1319 a h
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c1301 := derived1301 a h
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c1320 := derived1320 a h
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c1316 := derived1316 a h
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c70 := h 69 (by decide)
  have h19 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1321, some c280, some c56, some c296, some c1313, some c40, some c701, some c1277, some c83, some c319, some c139, some c3, some c11, some c1311, some c135, some c107, some c147, some c19, some c384, some c21, some c180, some c305, some c237, some c290, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c1299, c99, c100, c1321, c280, c56, c296, c1313, c40, c701, c1277, c83, c319, c139, c3, c11, c1311, c135, c107, c147, c19, c384, c21, c180, c305, c237, c290] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1321 := derived1321 a h
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c1313 := derived1313 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c701 := derived701 a h
  have h10 : Entails.eval a c1277 := derived1277 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c1311 := derived1311 a h
  have h17 : Entails.eval a c135 := h 134 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c384 := h 383 (by decide)
  have h22 : Entails.eval a c21 := h 20 (by decide)
  have h23 : Entails.eval a c180 := h 179 (by decide)
  have h24 : Entails.eval a c305 := h 304 (by decide)
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨39, by decide⟩, true), (⟨25, by decide⟩, true), (⟨37, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1311, some c202, some c3, some c27, some c119, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1311, c202, c3, c27, c119] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1311 := derived1311 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1323, some c19, some c119, some c3, some c11, some c142, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1323, c19, c119, c3, c11, c142] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1323 := derived1323 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1321, some c319, some c1299, some c1322, some c313, some c282, some c1324, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c1321, c319, c1299, c1322, c313, c282, c1324] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c1321 := derived1321 a h
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c1299 := derived1299 a h
  have h3 : Entails.eval a c1322 := derived1322 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c1324 := derived1324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1321, some c1277, some c1325, some c57, some c296, some c56, some c1299, some c99, some c71, some c1312, some c1300, some c95, some c701, some c139, some c3, some c1320, some c19, some c1316, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c100, c1321, c1277, c1325, c57, c296, c56, c1299, c99, c71, c1312, c1300, c95, c701, c139, c3, c1320, c19, c1316] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1321 := derived1321 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c296 := h 295 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c1299 := derived1299 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1312 := derived1312 a h
  have h11 : Entails.eval a c1300 := derived1300 a h
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c701 := derived701 a h
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c1320 := derived1320 a h
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c1316 := derived1316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1299, some c99, some c1321, some c1277, some c1325, some c57, some c296, some c81, some c319, some c1326, some c40, some c701, some c139, some c11, some c135, some c107, some c147, some c27, some c253, some c180, some c240, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c100, c1299, c99, c1321, c1277, c1325, c57, c296, c81, c319, c1326, c40, c701, c139, c11, c135, c107, c147, c27, c253, c180, c240] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1321 := derived1321 a h
  have h4 : Entails.eval a c1277 := derived1277 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c1326 := derived1326 a h
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c701 := derived701 a h
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c135 := h 134 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c27 := h 26 (by decide)
  have h19 : Entails.eval a c253 := h 252 (by decide)
  have h20 : Entails.eval a c180 := h 179 (by decide)
  have h21 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c27, some c202, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c19, c27, c202] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c125, some c250, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c185, c125, c250] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c135, some c107, some c253, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c135, c107, c253] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c135 := h 134 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c1321, some c319, some c1325, some c57, some c71, some c296, some c1327, some c313, some c298, some c1301, some c40, some c701, some c1328, some c240, some c1330, some c11, some c5, some c1329, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c1299, c99, c100, c1277, c1321, c319, c1325, c57, c71, c296, c1327, c313, c298, c1301, c40, c701, c1328, c240, c1330, c11, c5, c1329] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1321 := derived1321 a h
  have h5 : Entails.eval a c319 := h 318 (by decide)
  have h6 : Entails.eval a c1325 := derived1325 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c1327 := derived1327 a h
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c1301 := derived1301 a h
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c701 := derived701 a h
  have h16 : Entails.eval a c1328 := derived1328 a h
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c1330 := derived1330 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c5 := h 4 (by decide)
  have h21 : Entails.eval a c1329 := derived1329 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1299, some c99, some c1331, some c93, some c701, some c36, some c319, some c139, some c3, some c11, some c107, some c21, some c27, some c205, some c317, some c146, some c312, some c386, some c382, some c183, some c181, some c197, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c100, c1299, c99, c1331, c93, c701, c36, c319, c139, c3, c11, c107, c21, c27, c205, c317, c146, c312, c386, c382, c183, c181, c197] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1331 := derived1331 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c386 := h 385 (by decide)
  have h19 : Entails.eval a c382 := h 381 (by decide)
  have h20 : Entails.eval a c183 := h 182 (by decide)
  have h21 : Entails.eval a c181 := h 180 (by decide)
  have h22 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c282, some c1324, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c313, c282, c1324] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c1324 := derived1324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c107, some c207, some c5, some c185, some c125, some c252, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c701, c107, c207, c5, c185, c125, c252] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨48, by decide⟩, false), (⟨32, by decide⟩, true), (⟨47, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1334, some c21, some c125, some c237, some c5, some c172, some c147, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c1334, c21, c125, c237, c5, c172, c147] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c1334 := derived1334 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c1331, some c36, some c93, some c319, some c1332, some c313, some c1328, some c1333, some c57, some c71, some c296, some c298, some c1301, some c81, some c1335, some c3, some c11, some c142, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1299, c99, c100, c1277, c1331, c36, c93, c319, c1332, c313, c1328, c1333, c57, c71, c296, c298, c1301, c81, c1335, c3, c11, c142] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1331 := derived1331 a h
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c1332 := derived1332 a h
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c1328 := derived1328 a h
  have h11 : Entails.eval a c1333 := derived1333 a h
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c298 := h 297 (by decide)
  have h16 : Entails.eval a c1301 := derived1301 a h
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c1335 := derived1335 a h
  have h19 : Entails.eval a c3 := h 2 (by decide)
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c2, some c164, some c152, some c283, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c3, c2, c164, c152, c283] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c1336, some c51, some c37, some c344, some c56, some c69, some c368, some c1309, some c83, some c1307, some c1337, some c1320, some c19, some c1316, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c1299, c99, c100, c1277, c1336, c51, c37, c344, c56, c69, c368, c1309, c83, c1307, c1337, c1320, c19, c1316] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1336 := derived1336 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c1309 := derived1309 a h
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c1307 := derived1307 a h
  have h14 : Entails.eval a c1337 := derived1337 a h
  have h15 : Entails.eval a c1320 := derived1320 a h
  have h16 : Entails.eval a c19 := h 18 (by decide)
  have h17 : Entails.eval a c1316 := derived1316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1277, some c1336, some c37, some c387, some c1299, some c99, some c51, some c1338, some c57, some c71, some c368, some c1305, some c56, some c1300, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c100, c1277, c1336, c37, c387, c1299, c99, c51, c1338, c57, c71, c368, c1305, c56, c1300] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1336 := derived1336 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c1299 := derived1299 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c1338 := derived1338 a h
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c1305 := derived1305 a h
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c1300 := derived1300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨31, by decide⟩, false), (⟨52, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c56, some c69, some c368, some c284, some c83, some c1307, some c300, some c219, some c19, some c1320, some c3, some c2, some c164, some c777, some c283, some c781, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c99, c56, c69, c368, c284, c83, c1307, c300, c219, c19, c1320, c3, c2, c164, c777, c283, c781] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c1307 := derived1307 a h
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c1320 := derived1320 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c164 := h 163 (by decide)
  have h14 : Entails.eval a c777 := derived777 a h
  have h15 : Entails.eval a c283 := h 282 (by decide)
  have h16 : Entails.eval a c781 := derived781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c1336, some c51, some c37, some c1339, some c1340, some c344, some c57, some c71, some c368, some c284, some c1300, some c81, some c300, some c219, some c19, some c1320, some c3, some c2, some c164, some c777, some c283, some c781, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c1299, c99, c100, c1277, c1336, c51, c37, c1339, c1340, c344, c57, c71, c368, c284, c1300, c81, c300, c219, c19, c1320, c3, c2, c164, c777, c283, c781] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1336 := derived1336 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1339 := derived1339 a h
  have h8 : Entails.eval a c1340 := derived1340 a h
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  have h14 : Entails.eval a c1300 := derived1300 a h
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c300 := h 299 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c19 := h 18 (by decide)
  have h19 : Entails.eval a c1320 := derived1320 a h
  have h20 : Entails.eval a c3 := h 2 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c164 := h 163 (by decide)
  have h23 : Entails.eval a c777 := derived777 a h
  have h24 : Entails.eval a c283 := h 282 (by decide)
  have h25 : Entails.eval a c781 := derived781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c3, some c19, some c27, some c122, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c11, c3, c19, c27, c122] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨48, by decide⟩, false), (⟨45, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c82, some c299, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c50, c82, c299] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨6, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1320, some c1316, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1320, c1316] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1320 := derived1320 a h
  have h1 : Entails.eval a c1316 := derived1316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c100, some c99, some c1341, some c93, some c701, some c139, some c1342, some c11, some c3, some c1277, some c1336, some c51, some c83, some c1343, some c1344, some c69, some c355, some c154, some c159, some c349, some c180, some c219, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c1299, c100, c99, c1341, c93, c701, c139, c1342, c11, c3, c1277, c1336, c51, c83, c1343, c1344, c69, c355, c154, c159, c349, c180, c219] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1341 := derived1341 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c1342 := derived1342 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1277 := derived1277 a h
  have h11 : Entails.eval a c1336 := derived1336 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c1343 := derived1343 a h
  have h15 : Entails.eval a c1344 := derived1344 a h
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c355 := h 354 (by decide)
  have h18 : Entails.eval a c154 := h 153 (by decide)
  have h19 : Entails.eval a c159 := h 158 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  have h21 : Entails.eval a c180 := h 179 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1345, some c1299, some c100, some c99, some c1341, some c93, some c701, some c139, some c1342, some c3, some c1277, some c1336, some c51, some c37, some c1309, some c1320, some c1344, some c219, some c50, some c178, some c314, some c109, some c715, some c245, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c1345, c1299, c100, c99, c1341, c93, c701, c139, c1342, c3, c1277, c1336, c51, c37, c1309, c1320, c1344, c219, c50, c178, c314, c109, c715, c245] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c1345 := derived1345 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1341 := derived1341 a h
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c701 := derived701 a h
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c1342 := derived1342 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1277 := derived1277 a h
  have h11 : Entails.eval a c1336 := derived1336 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c1309 := derived1309 a h
  have h15 : Entails.eval a c1320 := derived1320 a h
  have h16 : Entails.eval a c1344 := derived1344 a h
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c50 := h 49 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c314 := h 313 (by decide)
  have h21 : Entails.eval a c109 := h 108 (by decide)
  have h22 : Entails.eval a c715 := derived715 a h
  have h23 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c100, some c99, some c1341, some c93, some c701, some c139, some c1342, some c11, some c3, some c1346, some c60, some c69, some c355, some c154, some c159, some c349, some c180, some c219, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c1299, c100, c99, c1341, c93, c701, c139, c1342, c11, c3, c1346, c60, c69, c355, c154, c159, c349, c180, c219] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1341 := derived1341 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c1342 := derived1342 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1346 := derived1346 a h
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1299, some c99, some c1341, some c93, some c701, some c1277, some c1336, some c51, some c139, some c3, some c1342, some c1347, some c71, some c1344, some c50, some c70, some c283, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c100, c1299, c99, c1341, c93, c701, c1277, c1336, c51, c139, c3, c1342, c1347, c71, c1344, c50, c70, c283] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1341 := derived1341 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c1277 := derived1277 a h
  have h7 : Entails.eval a c1336 := derived1336 a h
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c1342 := derived1342 a h
  have h12 : Entails.eval a c1347 := derived1347 a h
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c1344 := derived1344 a h
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨31, by decide⟩, false), (⟨56, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c781, some c283, some c164, some c197, some c185, some c157, some c340, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c701, c781, c283, c164, c197, c185, c157, c340] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c781 := derived781 a h
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c185 := h 184 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c19, some c99, some c100, some c1277, some c1336, some c51, some c1348, some c315, some c1341, some c36, some c1328, some c316, some c201, some c93, some c701, some c1342, some c188, some c27, some c798, some c1349, some c69, some c355, some c115, some c227, some c5, some c252, some c185, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c1299, c19, c99, c100, c1277, c1336, c51, c1348, c315, c1341, c36, c1328, c316, c201, c93, c701, c1342, c188, c27, c798, c1349, c69, c355, c115, c227, c5, c252, c185] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1277 := derived1277 a h
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c1348 := derived1348 a h
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c1341 := derived1341 a h
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c1328 := derived1328 a h
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c93 := h 92 (by decide)
  have h15 : Entails.eval a c701 := derived701 a h
  have h16 : Entails.eval a c1342 := derived1342 a h
  have h17 : Entails.eval a c188 := h 187 (by decide)
  have h18 : Entails.eval a c27 := h 26 (by decide)
  have h19 : Entails.eval a c798 := derived798 a h
  have h20 : Entails.eval a c1349 := derived1349 a h
  have h21 : Entails.eval a c69 := h 68 (by decide)
  have h22 : Entails.eval a c355 := h 354 (by decide)
  have h23 : Entails.eval a c115 := h 114 (by decide)
  have h24 : Entails.eval a c227 := h 226 (by decide)
  have h25 : Entails.eval a c5 := h 4 (by decide)
  have h26 : Entails.eval a c252 := h 251 (by decide)
  have h27 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c1336, some c51, some c1348, some c315, some c1341, some c93, some c701, some c36, some c19, some c1342, some c1328, some c188, some c316, some c201, some c1350, some c71, some c284, some c1349, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1299, c99, c100, c1277, c1336, c51, c1348, c315, c1341, c93, c701, c36, c19, c1342, c1328, c188, c316, c201, c1350, c71, c284, c1349] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1336 := derived1336 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c1348 := derived1348 a h
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c1341 := derived1341 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c701 := derived701 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c1342 := derived1342 a h
  have h14 : Entails.eval a c1328 := derived1328 a h
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  have h17 : Entails.eval a c201 := h 200 (by decide)
  have h18 : Entails.eval a c1350 := derived1350 a h
  have h19 : Entails.eval a c71 := h 70 (by decide)
  have h20 : Entails.eval a c284 := h 283 (by decide)
  have h21 : Entails.eval a c1349 := derived1349 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, true), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c349, some c356, some c105, some c798, some c213, some c21, some c168, some c125, some c159, some c5, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c119, c349, c356, c105, c798, c213, c21, c168, c125, c159, c5] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c798 := derived798 a h
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c315, some c133, some c154, some c756, some c199, some c109, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c51, c315, c133, c154, c756, c199, c109] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c756 := derived756 a h
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c18, some c132, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c2, c18, c132] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1351, some c1299, some c99, some c100, some c1277, some c1336, some c51, some c1348, some c315, some c1341, some c93, some c701, some c36, some c188, some c801, some c119, some c60, some c69, some c356, some c349, some c1352, some c1353, some c1354, some c50, some c281, some c299, some c58, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 57) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c1351, c1299, c99, c100, c1277, c1336, c51, c1348, c315, c1341, c93, c701, c36, c188, c801, c119, c60, c69, c356, c349, c1352, c1353, c1354, c50, c281, c299, c58] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1277 := derived1277 a h
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c1348 := derived1348 a h
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c1341 := derived1341 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c701 := derived701 a h
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c188 := h 187 (by decide)
  have h14 : Entails.eval a c801 := derived801 a h
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c60 := h 59 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c1352 := derived1352 a h
  have h21 : Entails.eval a c1353 := derived1353 a h
  have h22 : Entails.eval a c1354 := derived1354 a h
  have h23 : Entails.eval a c50 := h 49 (by decide)
  have h24 : Entails.eval a c281 := h 280 (by decide)
  have h25 : Entails.eval a c299 := h 298 (by decide)
  have h26 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1299, some c99, some c100, some c1277, some c1336, some c51, some c1348, some c315, some c1341, some c93, some c701, some c36, some c37, some c1355, some c3, some c11, some c715, some c105, some c142, some c333, some c382, some c245, some c316, some c154, some c109, some c141, some c277, some c342, some c918, some c155, some c197, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 57) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c1299, c99, c100, c1277, c1336, c51, c1348, c315, c1341, c93, c701, c36, c37, c1355, c3, c11, c715, c105, c142, c333, c382, c245, c316, c154, c109, c141, c277, c342, c918, c155, c197] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c1299 := derived1299 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1336 := derived1336 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c1348 := derived1348 a h
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c1341 := derived1341 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c701 := derived701 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c1355 := derived1355 a h
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c715 := derived715 a h
  have h17 : Entails.eval a c105 := h 104 (by decide)
  have h18 : Entails.eval a c142 := h 141 (by decide)
  have h19 : Entails.eval a c333 := h 332 (by decide)
  have h20 : Entails.eval a c382 := h 381 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c316 := h 315 (by decide)
  have h23 : Entails.eval a c154 := h 153 (by decide)
  have h24 : Entails.eval a c109 := h 108 (by decide)
  have h25 : Entails.eval a c141 := h 140 (by decide)
  have h26 : Entails.eval a c277 := h 276 (by decide)
  have h27 : Entails.eval a c342 := h 341 (by decide)
  have h28 : Entails.eval a c918 := derived918 a h
  have h29 : Entails.eval a c155 := h 154 (by decide)
  have h30 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1277, some c1299, some c99, some c1336, some c37, some c51, some c1348, some c315, some c1351, some c1356, some c57, some c71, some c284, some c801, some c219, some c3, some c715, some c178, some c105, some c245, some c109, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 57) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c100, c1277, c1299, c99, c1336, c37, c51, c1348, c315, c1351, c1356, c57, c71, c284, c801, c219, c3, c715, c178, c105, c245, c109] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1299 := derived1299 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1336 := derived1336 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c1348 := derived1348 a h
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c1351 := derived1351 a h
  have h10 : Entails.eval a c1356 := derived1356 a h
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  have h14 : Entails.eval a c801 := derived801 a h
  have h15 : Entails.eval a c219 := h 218 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c715 := derived715 a h
  have h18 : Entails.eval a c178 := h 177 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c245 := h 244 (by decide)
  have h21 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c908, some c99, some c91, some c95, some c388, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 57) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c701, c908, c99, c91, c95, c388] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c91, some c388, some c1242, some c95, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 57) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c701, c91, c388, c1242, c95] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c1242 := derived1242 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨37, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c72, some c356, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 57) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c66, c72, c356] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨38, by decide⟩, false), (⟨15, by decide⟩, true), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c139, some c1358, some c1359, some c98, some c52, some c753, some c318, some c283, some c145, some c8, some c120, some c24, some c20, some c201, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 57) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c1357, c139, c1358, c1359, c98, c52, c753, c318, c283, c145, c8, c120, c24, c20, c201] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c1358 := derived1358 a h
  have h3 : Entails.eval a c1359 := derived1359 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c753 := derived753 a h
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c139, some c701, some c1358, some c1359, some c98, some c52, some c1360, some c1361, some c140, some c8, some c4, some c145, some c275, some c157, some c153, some c349, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 57) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c1357, c139, c701, c1358, c1359, c98, c52, c1360, c1361, c140, c8, c4, c145, c275, c157, c153, c349] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c1358 := derived1358 a h
  have h4 : Entails.eval a c1359 := derived1359 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c1360 := derived1360 a h
  have h8 : Entails.eval a c1361 := derived1361 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c145 := h 144 (by decide)
  have h13 : Entails.eval a c275 := h 274 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1362, some c1357, some c1359, some c39, some c908, some c19, some c3, some c1311, some c105, some c113, some c51, some c272, some c314, some c67, some c50, some c355, some c101, some c69, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 57) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1362, c1357, c1359, c39, c908, c19, c3, c1311, c105, c113, c51, c272, c314, c67, c50, c355, c101, c69] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c1311 := derived1311 a h
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c314 := h 313 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c355 := h 354 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨25, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c247, some c120, some c133, some c4, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 57) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c20, c247, c120, c133, c4] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨38, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c283, some c318, some c1364, some c105, some c201, some c4, some c24, some c120, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 57) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c314, c283, c318, c1364, c105, c201, c4, c24, c120] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c1364 := derived1364 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c354, some c153, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 57) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c350, c354, c153] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c113, some c270, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 57) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c105, c113, c270] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1362, some c1357, some c1363, some c99, some c98, some c39, some c52, some c1360, some c701, some c1365, some c140, some c8, some c4, some c1366, some c1367, some c20, some c261, some c247, some c765, some c1364, some c211, some c181, some c180, some c269, some c59, some c153, some c346, some c339, some c1242, some c94, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 57) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c1362, c1357, c1363, c99, c98, c39, c52, c1360, c701, c1365, c140, c8, c4, c1366, c1367, c20, c261, c247, c765, c1364, c211, c181, c180, c269, c59, c153, c346, c339, c1242, c94] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1363 := derived1363 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c1360 := derived1360 a h
  have h8 : Entails.eval a c701 := derived701 a h
  have h9 : Entails.eval a c1365 := derived1365 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c1366 := derived1366 a h
  have h14 : Entails.eval a c1367 := derived1367 a h
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c247 := h 246 (by decide)
  have h18 : Entails.eval a c765 := derived765 a h
  have h19 : Entails.eval a c1364 := derived1364 a h
  have h20 : Entails.eval a c211 := h 210 (by decide)
  have h21 : Entails.eval a c181 := h 180 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  have h23 : Entails.eval a c269 := h 268 (by decide)
  have h24 : Entails.eval a c59 := h 58 (by decide)
  have h25 : Entails.eval a c153 := h 152 (by decide)
  have h26 : Entails.eval a c346 := h 345 (by decide)
  have h27 : Entails.eval a c339 := h 338 (by decide)
  have h28 : Entails.eval a c1242 := derived1242 a h
  have h29 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, true), (⟨31, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1359, some c39, some c908, some c702, some c314, some c726, some c212, some c50, some c319, some c308, some c208, some c257, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 57) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c1359, c39, c908, c702, c314, c726, c212, c50, c319, c308, c208, c257] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c1359 := derived1359 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c702 := derived702 a h
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c726 := derived726 a h
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨23, by decide⟩, true), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c212, some c312, some c246, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p1370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 57) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c212, c312, c246] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c212 := h 211 (by decide)
  have h1 : Entails.eval a c312 := h 311 (by decide)
  have h2 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1362, some c1357, some c1359, some c39, some c3, some c908, some c1368, some c1320, some c1344, some c1369, some c715, some c1370, some c283, some c66, some c58, some c356, some c299, some c219, some c83, some c79, some c380, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 57) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c1362, c1357, c1359, c39, c3, c908, c1368, c1320, c1344, c1369, c715, c1370, c283, c66, c58, c356, c299, c219, c83, c79, c380] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c908 := derived908 a h
  have h6 : Entails.eval a c1368 := derived1368 a h
  have h7 : Entails.eval a c1320 := derived1320 a h
  have h8 : Entails.eval a c1344 := derived1344 a h
  have h9 : Entails.eval a c1369 := derived1369 a h
  have h10 : Entails.eval a c715 := derived715 a h
  have h11 : Entails.eval a c1370 := derived1370 a h
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c356 := h 355 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c83 := h 82 (by decide)
  have h19 : Entails.eval a c79 := h 78 (by decide)
  have h20 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1362, some c1357, some c1359, some c39, some c3, some c1368, some c1371, some c67, some c356, some c355, some c69, some c228, some c101, some c22, some c1369, some c205, some c715, some c105, some c318, some c1370, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 57) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c1362, c1357, c1359, c39, c3, c1368, c1371, c67, c356, c355, c69, c228, c101, c22, c1369, c205, c715, c105, c318, c1370] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c1368 := derived1368 a h
  have h6 : Entails.eval a c1371 := derived1371 a h
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c1369 := derived1369 a h
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c715 := derived715 a h
  have h17 : Entails.eval a c105 := h 104 (by decide)
  have h18 : Entails.eval a c318 := h 317 (by decide)
  have h19 : Entails.eval a c1370 := derived1370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1368, some c1357, some c1359, some c39, some c908, some c1372, some c47, some c51, some c319, some c278, some c49, some c500, some c55, some c67, some c101, some c205, some c289, some c723, some c214, some c354, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 57) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c1368, c1357, c1359, c39, c908, c1372, c47, c51, c319, c278, c49, c500, c55, c67, c101, c205, c289, c723, c214, c354] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c1368 := derived1368 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c1372 := derived1372 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c500 := derived500 a h
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c723 := derived723 a h
  have h18 : Entails.eval a c214 := h 213 (by decide)
  have h19 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1373, some c99, some c98, some c1360, some c52, some c1368, some c1362, some c753, some c318, some c283, some c205, some c24, some c120, some c220, some c180, some c767, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 57) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c1357, c1373, c99, c98, c1360, c52, c1368, c1362, c753, c318, c283, c205, c24, c120, c220, c180, c767] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1373 := derived1373 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1360 := derived1360 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c1368 := derived1368 a h
  have h7 : Entails.eval a c1362 := derived1362 a h
  have h8 : Entails.eval a c753 := derived753 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c767 := derived767 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1362, some c1368, some c1373, some c99, some c98, some c39, some c52, some c1360, some c701, some c1374, some c140, some c8, some c4, some c1366, some c1367, some c20, some c765, some c180, some c59, some c84, some c349, some c378, some c511, some c153, some c237, some c22, some c275, some c788, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 57) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c1357, c1362, c1368, c1373, c99, c98, c39, c52, c1360, c701, c1374, c140, c8, c4, c1366, c1367, c20, c765, c180, c59, c84, c349, c378, c511, c153, c237, c22, c275, c788] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1362 := derived1362 a h
  have h2 : Entails.eval a c1368 := derived1368 a h
  have h3 : Entails.eval a c1373 := derived1373 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c1360 := derived1360 a h
  have h9 : Entails.eval a c701 := derived701 a h
  have h10 : Entails.eval a c1374 := derived1374 a h
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c1366 := derived1366 a h
  have h15 : Entails.eval a c1367 := derived1367 a h
  have h16 : Entails.eval a c20 := h 19 (by decide)
  have h17 : Entails.eval a c765 := derived765 a h
  have h18 : Entails.eval a c180 := h 179 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c84 := h 83 (by decide)
  have h21 : Entails.eval a c349 := h 348 (by decide)
  have h22 : Entails.eval a c378 := h 377 (by decide)
  have h23 : Entails.eval a c511 := derived511 a h
  have h24 : Entails.eval a c153 := h 152 (by decide)
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c22 := h 21 (by decide)
  have h27 : Entails.eval a c275 := h 274 (by decide)
  have h28 : Entails.eval a c788 := derived788 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1375, some c1357, some c1359, some c39, some c908, some c71, some c139, some c3, some c1320, some c19, some c1316, some c70, some c1369, some c283, some c715, some c1370, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 57) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c1375, c1357, c1359, c39, c908, c71, c139, c3, c1320, c19, c1316, c70, c1369, c283, c715, c1370] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c1320 := derived1320 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c1316 := derived1316 a h
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c1369 := derived1369 a h
  have h13 : Entails.eval a c283 := h 282 (by decide)
  have h14 : Entails.eval a c715 := derived715 a h
  have h15 : Entails.eval a c1370 := derived1370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1375, some c1357, some c1359, some c39, some c908, some c57, some c71, some c1376, some c47, some c51, some c319, some c294, some c49, some c79, some c101, some c70, some c78, some c350, some c354, some c374, some c378, some c321, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 57) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c1375, c1357, c1359, c39, c908, c57, c71, c1376, c47, c51, c319, c294, c49, c79, c101, c70, c78, c350, c354, c374, c378, c321] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c1376 := derived1376 a h
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c294 := h 293 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c350 := h 349 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c378 := h 377 (by decide)
  have h21 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨37, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c72, some c70, some c1027, some c343, some c35, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 57) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c66, c72, c70, c1027, c343, c35] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c1027 := derived1027 a h
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1375, some c1377, some c99, some c98, some c39, some c1378, some c52, some c753, some c318, some c1361, some c283, some c1365, some c205, some c24, some c120, some c220, some c180, some c767, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 57) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c1357, c1375, c1377, c99, c98, c39, c1378, c52, c753, c318, c1361, c283, c1365, c205, c24, c120, c220, c180, c767] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1377 := derived1377 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c1378 := derived1378 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c753 := derived753 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c1361 := derived1361 a h
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c1365 := derived1365 a h
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c767 := derived767 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1375, some c1377, some c99, some c98, some c39, some c52, some c701, some c1378, some c1379, some c140, some c8, some c4, some c1366, some c1367, some c20, some c765, some c231, some c261, some c111, some c180, some c84, some c378, some c511, some c237, some c22, some c209, some c229, some c281, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 57) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c1357, c1375, c1377, c99, c98, c39, c52, c701, c1378, c1379, c140, c8, c4, c1366, c1367, c20, c765, c231, c261, c111, c180, c84, c378, c511, c237, c22, c209, c229, c281] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1377 := derived1377 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c1378 := derived1378 a h
  have h9 : Entails.eval a c1379 := derived1379 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c1366 := derived1366 a h
  have h14 : Entails.eval a c1367 := derived1367 a h
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c765 := derived765 a h
  have h17 : Entails.eval a c231 := h 230 (by decide)
  have h18 : Entails.eval a c261 := h 260 (by decide)
  have h19 : Entails.eval a c111 := h 110 (by decide)
  have h20 : Entails.eval a c180 := h 179 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c378 := h 377 (by decide)
  have h23 : Entails.eval a c511 := derived511 a h
  have h24 : Entails.eval a c237 := h 236 (by decide)
  have h25 : Entails.eval a c22 := h 21 (by decide)
  have h26 : Entails.eval a c209 := h 208 (by decide)
  have h27 : Entails.eval a c229 := h 228 (by decide)
  have h28 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c315, some c105, some c3, some c2, some c164, some c777, some c283, some c781, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 57) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c284, c315, c105, c3, c2, c164, c777, c283, c781] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c777 := derived777 a h
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c781 := derived781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1380, some c284, some c1381, some c19, some c18, some c801, some c232, some c3, some c283, some c1366, some c110, some c7, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 57) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c1380, c284, c1381, c19, c18, c801, c232, c3, c283, c1366, c110, c7] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c1380 := derived1380 a h
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c1381 := derived1381 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c801 := derived801 a h
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c1366 := derived1366 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1382, some c1380, some c284, some c315, some c908, some c1357, some c19, some c105, some c780, some c3, some c283, some c66, some c58, some c164, some c355, some c299, some c160, some c83, some c79, some c177, some c380, some c328, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 57) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1382, c1380, c284, c315, c908, c1357, c19, c105, c780, c3, c283, c66, c58, c164, c355, c299, c160, c83, c79, c177, c380, c328] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1382 := derived1382 a h
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c780 := derived780 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c164 := h 163 (by decide)
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c299 := h 298 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c83 := h 82 (by decide)
  have h18 : Entails.eval a c79 := h 78 (by decide)
  have h19 : Entails.eval a c177 := h 176 (by decide)
  have h20 : Entails.eval a c380 := h 379 (by decide)
  have h21 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c83, some c79, some c380, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 57) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c300, c83, c79, c380] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1380, some c908, some c1384, some c284, some c1383, some c219, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 57) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c1357, c1380, c908, c1384, c284, c1383, c219] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1384 := derived1384 a h
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c1383 := derived1383 a h
  have h6 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1380, some c908, some c1384, some c315, some c1385, some c67, some c60, some c356, some c355, some c219, some c69, some c328, some c19, some c101, some c780, some c299, some c78, some c82, some c379, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 57) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c1357, c1380, c908, c1384, c315, c1385, c67, c60, c356, c355, c219, c69, c328, c19, c101, c780, c299, c78, c82, c379] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1384 := derived1384 a h
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c1385 := derived1385 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c780 := derived780 a h
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c82 := h 81 (by decide)
  have h19 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c1380, some c1357, some c315, some c1384, some c1386, some c71, some c284, some c1382, some c219, some c70, some c19, some c283, some c780, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 57) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c908, c1380, c1357, c315, c1384, c1386, c71, c284, c1382, c219, c70, c19, c283, c780] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c1380 := derived1380 a h
  have h2 : Entails.eval a c1357 := derived1357 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c1384 := derived1384 a h
  have h5 : Entails.eval a c1386 := derived1386 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c1382 := derived1382 a h
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c780 := derived780 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1380, some c1357, some c908, some c1387, some c47, some c51, some c320, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 57) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c1380, c1357, c908, c1387, c47, c51, c320] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c1380 := derived1380 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1388

end CochromaticTwenty.Certificates.B16_7_2
