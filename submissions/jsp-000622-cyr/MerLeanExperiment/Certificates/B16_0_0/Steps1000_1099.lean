import MerLeanExperiment.Certificates.B16_0_0.Steps0900_0999

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1394 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c265, some c35, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 57) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c266, c265, c35] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c66, some c71, some c354, some c359, some c217, some c271, some c269, some c4, some c2, some c157, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 57) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c1394, c66, c71, c354, c359, c217, c271, c269, c4, c2, c157] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c217 := h 216 (by decide)
  have h6 : Entails.eval a c271 := h 270 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c1363, some c62, some c283, some c257, some c59, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 57) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c1394, c1363, c62, c283, c257, c59] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c1363 := derived1363 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c1236, some c360, some c21, some c57, some c251, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 57) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c257, c1236, c360, c21, c57, c251] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c1236 := derived1236 a h
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c553, some c1354, some c122, some c1395, some c121, some c205, some c16, some c4, some c166, some c160, some c222, some c1397, some c99, some c194, some c188, some c348, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 57) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c1394, c553, c1354, c122, c1395, c121, c205, c16, c4, c166, c160, c222, c1397, c99, c194, c188, c348] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c1354 := derived1354 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c1395 := derived1395 a h
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c1397 := derived1397 a h
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c553, some c1354, some c122, some c1398, some c271, some c269, some c23, some c4, some c21, some c2, some c157, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 57) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c1394, c553, c1354, c122, c1398, c271, c269, c23, c4, c21, c2, c157] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c1354 := derived1354 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c1398 := derived1398 a h
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1375, some c1393, some c1394, some c103, some c1399, some c115, some c40, some c113, some c1382, some c199, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 57) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c105, c1375, c1393, c1394, c103, c1399, c115, c40, c113, c1382, c199] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c1399 := derived1399 a h
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c1382 := derived1382 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true), (⟨38, by decide⟩, false), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c217, some c362, some c285, some c59, some c150, some c322, some c286, some c143, some c1234, some c565, some c385, some c57, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 57) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c357, c217, c362, c285, c59, c150, c322, c286, c143, c1234, c565, c385, c57] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c150 := h 149 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c286 := h 285 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c1234 := derived1234 a h
  have h10 : Entails.eval a c565 := derived565 a h
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c210, some c435, some c274, some c217, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 57) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c23, c210, c435, c274, c217] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c435 := derived435 a h
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨38, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c217, some c942, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 57) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c217, c942] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c217 := h 216 (by decide)
  have h1 : Entails.eval a c942 := derived942 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1404 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1375, some c1393, some c1394, some c553, some c1354, some c122, some c1395, some c113, some c40, some c1400, some c121, some c211, some c1401, some c1402, some c1403, some c1396, some c1397, some c43, some c59, some c138, some c162, some c283, some c240, some c135, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 57) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c105, c103, c1375, c1393, c1394, c553, c1354, c122, c1395, c113, c40, c1400, c121, c211, c1401, c1402, c1403, c1396, c1397, c43, c59, c138, c162, c283, c240, c135] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1375 := derived1375 a h
  have h3 : Entails.eval a c1393 := derived1393 a h
  have h4 : Entails.eval a c1394 := derived1394 a h
  have h5 : Entails.eval a c553 := derived553 a h
  have h6 : Entails.eval a c1354 := derived1354 a h
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c1395 := derived1395 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c1400 := derived1400 a h
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  have h14 : Entails.eval a c1401 := derived1401 a h
  have h15 : Entails.eval a c1402 := derived1402 a h
  have h16 : Entails.eval a c1403 := derived1403 a h
  have h17 : Entails.eval a c1396 := derived1396 a h
  have h18 : Entails.eval a c1397 := derived1397 a h
  have h19 : Entails.eval a c43 := h 42 (by decide)
  have h20 : Entails.eval a c59 := h 58 (by decide)
  have h21 : Entails.eval a c138 := h 137 (by decide)
  have h22 : Entails.eval a c162 := h 161 (by decide)
  have h23 : Entails.eval a c283 := h 282 (by decide)
  have h24 : Entails.eval a c240 := h 239 (by decide)
  have h25 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1375, some c1393, some c1394, some c103, some c553, some c1354, some c122, some c1404, some c271, some c269, some c23, some c4, some c21, some c2, some c157, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 57) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c105, c1375, c1393, c1394, c103, c553, c1354, c122, c1404, c271, c269, c23, c4, c21, c2, c157] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c553 := derived553 a h
  have h6 : Entails.eval a c1354 := derived1354 a h
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c1404 := derived1404 a h
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c4, some c435, some c153, some c217, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 57) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c23, c4, c435, c153, c217] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c435 := derived435 a h
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c71, some c359, some c354, some c217, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 57) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c66, c71, c359, c354, c217] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨45, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1330, some c181, some c190, some c79, some c363, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 57) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1330, c181, c190, c79, c363] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1330 := derived1330 a h
  have h1 : Entails.eval a c181 := h 180 (by decide)
  have h2 : Entails.eval a c190 := h 189 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1375, some c1393, some c1394, some c1405, some c115, some c40, some c113, some c126, some c1406, some c103, some c1407, some c1403, some c206, some c1400, some c1397, some c285, some c138, some c240, some c340, some c338, some c1408, some c16, some c172, some c135, some c76, some c309, some c372, some c363, some c182, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 57) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c105, c1375, c1393, c1394, c1405, c115, c40, c113, c126, c1406, c103, c1407, c1403, c206, c1400, c1397, c285, c138, c240, c340, c338, c1408, c16, c172, c135, c76, c309, c372, c363, c182] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c1405 := derived1405 a h
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c1406 := derived1406 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1407 := derived1407 a h
  have h12 : Entails.eval a c1403 := derived1403 a h
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c1400 := derived1400 a h
  have h15 : Entails.eval a c1397 := derived1397 a h
  have h16 : Entails.eval a c285 := h 284 (by decide)
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c240 := h 239 (by decide)
  have h19 : Entails.eval a c340 := h 339 (by decide)
  have h20 : Entails.eval a c338 := h 337 (by decide)
  have h21 : Entails.eval a c1408 := derived1408 a h
  have h22 : Entails.eval a c16 := h 15 (by decide)
  have h23 : Entails.eval a c172 := h 171 (by decide)
  have h24 : Entails.eval a c135 := h 134 (by decide)
  have h25 : Entails.eval a c76 := h 75 (by decide)
  have h26 : Entails.eval a c309 := h 308 (by decide)
  have h27 : Entails.eval a c372 := h 371 (by decide)
  have h28 : Entails.eval a c363 := h 362 (by decide)
  have h29 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1375, some c1393, some c1394, some c1405, some c115, some c40, some c113, some c103, some c126, some c206, some c1406, some c1407, some c1403, some c1409, some c59, some c99, some c1232, some c162, some c283, some c49, some c16, some c148, some c154, some c182, some c167, some c1234, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 57) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c105, c1375, c1393, c1394, c1405, c115, c40, c113, c103, c126, c206, c1406, c1407, c1403, c1409, c59, c99, c1232, c162, c283, c49, c16, c148, c154, c182, c167, c1234] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c1405 := derived1405 a h
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c1406 := derived1406 a h
  have h12 : Entails.eval a c1407 := derived1407 a h
  have h13 : Entails.eval a c1403 := derived1403 a h
  have h14 : Entails.eval a c1409 := derived1409 a h
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c99 := h 98 (by decide)
  have h17 : Entails.eval a c1232 := derived1232 a h
  have h18 : Entails.eval a c162 := h 161 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c49 := h 48 (by decide)
  have h21 : Entails.eval a c16 := h 15 (by decide)
  have h22 : Entails.eval a c148 := h 147 (by decide)
  have h23 : Entails.eval a c154 := h 153 (by decide)
  have h24 : Entails.eval a c182 := h 181 (by decide)
  have h25 : Entails.eval a c167 := h 166 (by decide)
  have h26 : Entails.eval a c1234 := derived1234 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1375, some c103, some c105, some c1393, some c1394, some c1405, some c115, some c40, some c113, some c1410, some c271, some c4, some c197, some c2, some c269, some c207, some c36, some c49, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 57) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c1375, c103, c105, c1393, c1394, c1405, c115, c40, c113, c1410, c271, c4, c197, c2, c269, c207, c36, c49] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c1393 := derived1393 a h
  have h4 : Entails.eval a c1394 := derived1394 a h
  have h5 : Entails.eval a c1405 := derived1405 a h
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c1410 := derived1410 a h
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c553, some c1354, some c122, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 57) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c553, c1354, c122] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c553 := derived553 a h
  have h1 : Entails.eval a c1354 := derived1354 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c121, some c1407, some c203, some c11, some c167, some c227, some c218, some c357, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 57) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c122, c121, c1407, c203, c11, c167, c227, c218, c357] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c1407 := derived1407 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨21, by decide⟩, false), (⟨43, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1348, some c66, some c71, some c354, some c218, some c159, some c2, some c233, some c268, some c133, some c316, some c280, some c214, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 57) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c1357, c1348, c66, c71, c354, c218, c159, c2, c233, c268, c133, c316, c280, c214] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1348 := derived1348 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1411, some c1348, some c1375, some c36, some c4, some c23, some c1357, some c113, some c122, some c1412, some c40, some c134, some c1413, some c1414, some c205, some c163, some c145, some c26, some c227, some c43, some c167, some c216, some c18, some c53, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 57) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c105, c103, c1411, c1348, c1375, c36, c4, c23, c1357, c113, c122, c1412, c40, c134, c1413, c1414, c205, c163, c145, c26, c227, c43, c167, c216, c18, c53] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1411 := derived1411 a h
  have h3 : Entails.eval a c1348 := derived1348 a h
  have h4 : Entails.eval a c1375 := derived1375 a h
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c1357 := derived1357 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c1412 := derived1412 a h
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c1413 := derived1413 a h
  have h15 : Entails.eval a c1414 := derived1414 a h
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c145 := h 144 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c227 := h 226 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c167 := h 166 (by decide)
  have h23 : Entails.eval a c216 := h 215 (by decide)
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c119, some c43, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 57) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c7, c119, c43] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1417 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1411, some c1348, some c1357, some c1412, some c1375, some c113, some c122, some c40, some c134, some c1413, some c1414, some c1416, some c1415, some c268, some c21, some c2, some c159, some c227, some c218, some c357, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 57) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c105, c103, c1411, c1348, c1357, c1412, c1375, c113, c122, c40, c134, c1413, c1414, c1416, c1415, c268, c21, c2, c159, c227, c218, c357] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1411 := derived1411 a h
  have h3 : Entails.eval a c1348 := derived1348 a h
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1412 := derived1412 a h
  have h6 : Entails.eval a c1375 := derived1375 a h
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c1413 := derived1413 a h
  have h12 : Entails.eval a c1414 := derived1414 a h
  have h13 : Entails.eval a c1416 := derived1416 a h
  have h14 : Entails.eval a c1415 := derived1415 a h
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c227 := h 226 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c200, some c16, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 57) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c199, c200, c16] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1419 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c52, some c24, some c5, some c165, some c285, some c227, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 57) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c206, c52, c24, c5, c165, c285, c227] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1411, some c1357, some c1348, some c1375, some c1417, some c1418, some c1416, some c207, some c131, some c1412, some c23, some c4, some c36, some c197, some c153, some c49, some c11, some c218, some c134, some c167, some c1353, some c61, some c182, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 57) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c105, c103, c1411, c1357, c1348, c1375, c1417, c1418, c1416, c207, c131, c1412, c23, c4, c36, c197, c153, c49, c11, c218, c134, c167, c1353, c61, c182] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1411 := derived1411 a h
  have h3 : Entails.eval a c1357 := derived1357 a h
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1375 := derived1375 a h
  have h6 : Entails.eval a c1417 := derived1417 a h
  have h7 : Entails.eval a c1418 := derived1418 a h
  have h8 : Entails.eval a c1416 := derived1416 a h
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c131 := h 130 (by decide)
  have h11 : Entails.eval a c1412 := derived1412 a h
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c197 := h 196 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  have h20 : Entails.eval a c134 := h 133 (by decide)
  have h21 : Entails.eval a c167 := h 166 (by decide)
  have h22 : Entails.eval a c1353 := derived1353 a h
  have h23 : Entails.eval a c61 := h 60 (by decide)
  have h24 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1411, some c1357, some c1348, some c1375, some c1417, some c1418, some c7, some c119, some c131, some c1416, some c1419, some c1420, some c268, some c21, some c2, some c151, some c159, some c218, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 57) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c105, c103, c1411, c1357, c1348, c1375, c1417, c1418, c7, c119, c131, c1416, c1419, c1420, c268, c21, c2, c151, c159, c218] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1411 := derived1411 a h
  have h3 : Entails.eval a c1357 := derived1357 a h
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1375 := derived1375 a h
  have h6 : Entails.eval a c1417 := derived1417 a h
  have h7 : Entails.eval a c1418 := derived1418 a h
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c131 := h 130 (by decide)
  have h11 : Entails.eval a c1416 := derived1416 a h
  have h12 : Entails.eval a c1419 := derived1419 a h
  have h13 : Entails.eval a c1420 := derived1420 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c151 := h 150 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1411, some c1348, some c1357, some c1412, some c113, some c40, some c134, some c122, some c1375, some c121, some c1407, some c203, some c11, some c2, some c963, some c167, some c233, some c1353, some c218, some c133, some c272, some c300, some c57, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 57) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c105, c103, c1411, c1348, c1357, c1412, c113, c40, c134, c122, c1375, c121, c1407, c203, c11, c2, c963, c167, c233, c1353, c218, c133, c272, c300, c57] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1411 := derived1411 a h
  have h3 : Entails.eval a c1348 := derived1348 a h
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1412 := derived1412 a h
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c1375 := derived1375 a h
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c1407 := derived1407 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c963 := derived963 a h
  have h17 : Entails.eval a c167 := h 166 (by decide)
  have h18 : Entails.eval a c233 := h 232 (by decide)
  have h19 : Entails.eval a c1353 := derived1353 a h
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c133 := h 132 (by decide)
  have h22 : Entails.eval a c272 := h 271 (by decide)
  have h23 : Entails.eval a c300 := h 299 (by decide)
  have h24 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨48, by decide⟩, true), (⟨21, by decide⟩, false), (⟨41, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c4, some c35, some c205, some c168, some c241, some c1239, some c260, some c191, some c99, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 57) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c271, c4, c35, c205, c168, c241, c1239, c260, c191, c99] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c241 := h 240 (by decide)
  have h6 : Entails.eval a c1239 := derived1239 a h
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1421, some c105, some c103, some c1411, some c1348, some c1357, some c1412, some c1375, some c113, some c40, some c134, some c76, some c1422, some c271, some c36, some c85, some c1423, some c146, some c43, some c319, some c318, some c12, some c1350, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 57) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1421, c105, c103, c1411, c1348, c1357, c1412, c1375, c113, c40, c134, c76, c1422, c271, c36, c85, c1423, c146, c43, c319, c318, c12, c1350] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1421 := derived1421 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c1411 := derived1411 a h
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c1412 := derived1412 a h
  have h7 : Entails.eval a c1375 := derived1375 a h
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c1422 := derived1422 a h
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c1423 := derived1423 a h
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c319 := h 318 (by decide)
  have h20 : Entails.eval a c318 := h 317 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c1350 := derived1350 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1375, some c1411, some c1357, some c1407, some c1424, some c1418, some c1348, some c1412, some c23, some c4, some c1406, some c1330, some c197, some c153, some c5, some c11, some c218, some c1055, some c167, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 57) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c105, c103, c1375, c1411, c1357, c1407, c1424, c1418, c1348, c1412, c23, c4, c1406, c1330, c197, c153, c5, c11, c218, c1055, c167] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1375 := derived1375 a h
  have h3 : Entails.eval a c1411 := derived1411 a h
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1407 := derived1407 a h
  have h6 : Entails.eval a c1424 := derived1424 a h
  have h7 : Entails.eval a c1418 := derived1418 a h
  have h8 : Entails.eval a c1348 := derived1348 a h
  have h9 : Entails.eval a c1412 := derived1412 a h
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c1406 := derived1406 a h
  have h13 : Entails.eval a c1330 := derived1330 a h
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c218 := h 217 (by decide)
  have h19 : Entails.eval a c1055 := derived1055 a h
  have h20 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c207, some c53, some c49, some c24, some c146, some c286, some c285, some c1397, some c324, some c218, some c59, some c144, some c153, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 57) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c206, c207, c53, c49, c24, c146, c286, c285, c1397, c324, c218, c59, c144, c153] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c286 := h 285 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c1397 := derived1397 a h
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c218 := h 217 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1407, some c1418, some c1348, some c1412, some c207, some c1426, some c1230, some c963, some c288, some c6, some c137, some c1334, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 57) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c1357, c1407, c1418, c1348, c1412, c207, c1426, c1230, c963, c288, c6, c137, c1334] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1407 := derived1407 a h
  have h2 : Entails.eval a c1418 := derived1418 a h
  have h3 : Entails.eval a c1348 := derived1348 a h
  have h4 : Entails.eval a c1412 := derived1412 a h
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c1426 := derived1426 a h
  have h7 : Entails.eval a c1230 := derived1230 a h
  have h8 : Entails.eval a c963 := derived963 a h
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c1334 := derived1334 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1428 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1375, some c1424, some c1418, some c103, some c1411, some c1348, some c1357, some c1412, some c40, some c146, some c43, some c318, some c1330, some c144, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 57) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c105, c1375, c1424, c1418, c103, c1411, c1348, c1357, c1412, c40, c146, c43, c318, c1330, c144] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1424 := derived1424 a h
  have h3 : Entails.eval a c1418 := derived1418 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c1411 := derived1411 a h
  have h6 : Entails.eval a c1348 := derived1348 a h
  have h7 : Entails.eval a c1357 := derived1357 a h
  have h8 : Entails.eval a c1412 := derived1412 a h
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c1330 := derived1330 a h
  have h14 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1428, some c1424, some c1421, some c1411, some c1375, some c103, some c105, some c1425, some c1427, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 57) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c1428, c1424, c1421, c1411, c1375, c103, c105, c1425, c1427] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1424 := derived1424 a h
  have h2 : Entails.eval a c1421 := derived1421 a h
  have h3 : Entails.eval a c1411 := derived1411 a h
  have h4 : Entails.eval a c1375 := derived1375 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1425 := derived1425 a h
  have h8 : Entails.eval a c1427 := derived1427 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c103, some c1375, some c1411, some c1348, some c1357, some c1412, some c1421, some c1424, some c1418, some c1428, some c207, some c1429, some c271, some c4, some c36, some c197, some c49, some c2, some c134, some c233, some c415, some c76, some c133, some c241, some c322, some c289, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 57) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c105, c103, c1375, c1411, c1348, c1357, c1412, c1421, c1424, c1418, c1428, c207, c1429, c271, c4, c36, c197, c49, c2, c134, c233, c415, c76, c133, c241, c322, c289] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1375 := derived1375 a h
  have h3 : Entails.eval a c1411 := derived1411 a h
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c1412 := derived1412 a h
  have h7 : Entails.eval a c1421 := derived1421 a h
  have h8 : Entails.eval a c1424 := derived1424 a h
  have h9 : Entails.eval a c1418 := derived1418 a h
  have h10 : Entails.eval a c1428 := derived1428 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c1429 := derived1429 a h
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c233 := h 232 (by decide)
  have h21 : Entails.eval a c415 := derived415 a h
  have h22 : Entails.eval a c76 := h 75 (by decide)
  have h23 : Entails.eval a c133 := h 132 (by decide)
  have h24 : Entails.eval a c241 := h 240 (by decide)
  have h25 : Entails.eval a c322 := h 321 (by decide)
  have h26 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c205, some c116, some c144, some c135, some c315, some c234, some c133, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 57) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c203, c205, c116, c144, c135, c315, c234, c133] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c106, some c1430, some c34, some c31, some c26, some c7, some c1348, some c1357, some c122, some c38, some c1412, some c113, some c41, some c1431, some c14, some c121, some c268, some c116, some c214, some c163, some c53, some c225, some c145, some c136, some c315, some c282, some c235, some c58, some c133, some c1310, some c159, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 57) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c104, c106, c1430, c34, c31, c26, c7, c1348, c1357, c122, c38, c1412, c113, c41, c1431, c14, c121, c268, c116, c214, c163, c53, c225, c145, c136, c315, c282, c235, c58, c133, c1310, c159] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c1348 := derived1348 a h
  have h8 : Entails.eval a c1357 := derived1357 a h
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c1412 := derived1412 a h
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c1431 := derived1431 a h
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c116 := h 115 (by decide)
  have h19 : Entails.eval a c214 := h 213 (by decide)
  have h20 : Entails.eval a c163 := h 162 (by decide)
  have h21 : Entails.eval a c53 := h 52 (by decide)
  have h22 : Entails.eval a c225 := h 224 (by decide)
  have h23 : Entails.eval a c145 := h 144 (by decide)
  have h24 : Entails.eval a c136 := h 135 (by decide)
  have h25 : Entails.eval a c315 := h 314 (by decide)
  have h26 : Entails.eval a c282 := h 281 (by decide)
  have h27 : Entails.eval a c235 := h 234 (by decide)
  have h28 : Entails.eval a c58 := h 57 (by decide)
  have h29 : Entails.eval a c133 := h 132 (by decide)
  have h30 : Entails.eval a c1310 := derived1310 a h
  have h31 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c6, some c961, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 57) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c25, c6, c961] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c961 := derived961 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c202, some c205, some c12, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 57) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c202, c205, c12] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c202 := h 201 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c104, some c106, some c1430, some c22, some c3, some c1354, some c1433, some c266, some c113, some c121, some c41, some c1363, some c317, some c273, some c1434, some c147, some c148, some c961, some c282, some c61, some c1234, some c260, some c386, some c98, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 57) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c1432, c104, c106, c1430, c22, c3, c1354, c1433, c266, c113, c121, c41, c1363, c317, c273, c1434, c147, c148, c961, c282, c61, c1234, c260, c386, c98] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1430 := derived1430 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c1354 := derived1354 a h
  have h7 : Entails.eval a c1433 := derived1433 a h
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c1363 := derived1363 a h
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c273 := h 272 (by decide)
  have h15 : Entails.eval a c1434 := derived1434 a h
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c961 := derived961 a h
  have h19 : Entails.eval a c282 := h 281 (by decide)
  have h20 : Entails.eval a c61 := h 60 (by decide)
  have h21 : Entails.eval a c1234 := derived1234 a h
  have h22 : Entails.eval a c260 := h 259 (by decide)
  have h23 : Entails.eval a c386 := h 385 (by decide)
  have h24 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c106, some c1430, some c1435, some c1348, some c1357, some c1412, some c113, some c121, some c122, some c15, some c41, some c203, some c1431, some c2, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 57) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c104, c106, c1430, c1435, c1348, c1357, c1412, c113, c121, c122, c15, c41, c203, c1431, c2] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c1435 := derived1435 a h
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c1412 := derived1412 a h
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c1431 := derived1431 a h
  have h14 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c266, some c1433, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 57) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1357, c266, c1433] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c1433 := derived1433 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1438 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c3, some c1412, some c269, some c21, some c2, some c156, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 57) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c22, c3, c1412, c269, c21, c2, c156] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1439 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c134, some c145, some c233, some c322, some c133, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 57) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c134, c145, c233, c322, c133] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c134 := h 133 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨25, by decide⟩, false), (⟨21, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c1439, some c315, some c133, some c233, some c235, some c173, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 57) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c2, c1439, c315, c133, c233, c235, c173] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c1439 := derived1439 a h
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨15, by decide⟩, false), (⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1412, some c1352, some c145, some c66, some c53, some c1062, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 57) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1348, c1412, c1352, c145, c66, c53, c1062] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1412 := derived1412 a h
  have h2 : Entails.eval a c1352 := derived1352 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1062 := derived1062 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1442 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c254, some c260, some c98, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 57) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c254, c260, c98] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c254 := h 253 (by decide)
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1443 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨24, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c282, some c218, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 57) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c273, c282, c218] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1444 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c106, some c104, some c1432, some c1436, some c271, some c1437, some c113, some c41, some c116, some c1434, some c1438, some c1348, some c214, some c1412, some c122, some c15, some c14, some c1440, some c1441, some c317, some c213, some c1442, some c61, some c94, some c1443, some c58, some c70, some c1310, some c384, some c357, some c159, some c1234, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 57) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c1430, c106, c104, c1432, c1436, c271, c1437, c113, c41, c116, c1434, c1438, c1348, c214, c1412, c122, c15, c14, c1440, c1441, c317, c213, c1442, c61, c94, c1443, c58, c70, c1310, c384, c357, c159, c1234] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c1432 := derived1432 a h
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c1437 := derived1437 a h
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c1434 := derived1434 a h
  have h11 : Entails.eval a c1438 := derived1438 a h
  have h12 : Entails.eval a c1348 := derived1348 a h
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c1412 := derived1412 a h
  have h15 : Entails.eval a c122 := h 121 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c1440 := derived1440 a h
  have h19 : Entails.eval a c1441 := derived1441 a h
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c213 := h 212 (by decide)
  have h22 : Entails.eval a c1442 := derived1442 a h
  have h23 : Entails.eval a c61 := h 60 (by decide)
  have h24 : Entails.eval a c94 := h 93 (by decide)
  have h25 : Entails.eval a c1443 := derived1443 a h
  have h26 : Entails.eval a c58 := h 57 (by decide)
  have h27 : Entails.eval a c70 := h 69 (by decide)
  have h28 : Entails.eval a c1310 := derived1310 a h
  have h29 : Entails.eval a c384 := h 383 (by decide)
  have h30 : Entails.eval a c357 := h 356 (by decide)
  have h31 : Entails.eval a c159 := h 158 (by decide)
  have h32 : Entails.eval a c1234 := derived1234 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1445 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1212, some c1357, some c21, some c2, some c22, some c3, some c156, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 57) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c1212, c1357, c21, c2, c22, c3, c156] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c1212 := derived1212 a h
  have h1 : Entails.eval a c1357 := derived1357 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1445, some c1438, some c1407, some c121, some c961, some c205, some c16, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 57) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c1445, c1438, c1407, c121, c961, c205, c16] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c1445 := derived1445 a h
  have h1 : Entails.eval a c1438 := derived1438 a h
  have h2 : Entails.eval a c1407 := derived1407 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c961 := derived961 a h
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1416, some c13, some c205, some c14, some c23, some c36, some c163, some c26, some c43, some c216, some c1440, some c53, some c157, some c145, some c1310, some c1443, some c58, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 57) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1430, c1416, c13, c205, c14, c23, c36, c163, c26, c43, c216, c1440, c53, c157, c145, c1310, c1443, c58] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1416 := derived1416 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c1440 := derived1440 a h
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c1310 := derived1310 a h
  have h16 : Entails.eval a c1443 := derived1443 a h
  have h17 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1444, some c1445, some c113, some c1416, some c1446, some c1348, some c1412, some c122, some c1413, some c13, some c1447, some c268, some c21, some c2, some c157, some c159, some c68, some c218, some c353, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 57) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c1430, c1444, c1445, c113, c1416, c1446, c1348, c1412, c122, c1413, c13, c1447, c268, c21, c2, c157, c159, c68, c218, c353] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1445 := derived1445 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c1416 := derived1416 a h
  have h5 : Entails.eval a c1446 := derived1446 a h
  have h6 : Entails.eval a c1348 := derived1348 a h
  have h7 : Entails.eval a c1412 := derived1412 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c1413 := derived1413 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c1447 := derived1447 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c68 := h 67 (by decide)
  have h18 : Entails.eval a c218 := h 217 (by decide)
  have h19 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1445, some c1438, some c1407, some c121, some c961, some c16, some c11, some c202, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 57) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c1445, c1438, c1407, c121, c961, c16, c11, c202] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c1445 := derived1445 a h
  have h1 : Entails.eval a c1438 := derived1438 a h
  have h2 : Entails.eval a c1407 := derived1407 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c961 := derived961 a h
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c205, some c1434, some c43, some c146, some c143, some c315, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 57) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c203, c205, c1434, c43, c146, c143, c315] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c1434 := derived1434 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c143 := h 142 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c1440, some c214, some c316, some c133, some c233, some c235, some c173, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 57) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c2, c1440, c214, c316, c133, c233, c235, c173] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c235 := h 234 (by decide)
  have h7 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1444, some c1430, some c1445, some c113, some c1448, some c1449, some c1348, some c1412, some c122, some c13, some c1450, some c121, some c271, some c23, some c1451, some c157, some c1310, some c57, some c96, some c185, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 57) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1444, c1430, c1445, c113, c1448, c1449, c1348, c1412, c122, c13, c1450, c121, c271, c23, c1451, c157, c1310, c57, c96, c185] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1444 := derived1444 a h
  have h1 : Entails.eval a c1430 := derived1430 a h
  have h2 : Entails.eval a c1445 := derived1445 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c1448 := derived1448 a h
  have h5 : Entails.eval a c1449 := derived1449 a h
  have h6 : Entails.eval a c1348 := derived1348 a h
  have h7 : Entails.eval a c1412 := derived1412 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c1450 := derived1450 a h
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c1451 := derived1451 a h
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c1310 := derived1310 a h
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1433, some c420, some c3, some c22, some c170, some c114, some c124, some c961, some c204, some c61, some c141, some c194, some c188, some c47, some c1239, some c369, some c1230, some c335, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 57) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c1433, c420, c3, c22, c170, c114, c124, c961, c204, c61, c141, c194, c188, c47, c1239, c369, c1230, c335] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c1433 := derived1433 a h
  have h1 : Entails.eval a c420 := derived420 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c961 := derived961 a h
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c194 := h 193 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c1239 := derived1239 a h
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c1230 := derived1230 a h
  have h17 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1454 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨39, by decide⟩, false), (⟨32, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c209, some c291, some c285, some c52, some c287, some c73, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 57) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c322, c209, c291, c285, c52, c287, c73] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1455 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1433, some c1444, some c1394, some c34, some c32, some c3, some c22, some c1212, some c1452, some c132, some c420, some c79, some c75, some c1453, some c201, some c156, some c141, some c1183, some c1454, some c140, some c202, some c16, some c17, some c961, some c110, some c71, some c73, some c362, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 57) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c1430, c1433, c1444, c1394, c34, c32, c3, c22, c1212, c1452, c132, c420, c79, c75, c1453, c201, c156, c141, c1183, c1454, c140, c202, c16, c17, c961, c110, c71, c73, c362] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1433 := derived1433 a h
  have h2 : Entails.eval a c1444 := derived1444 a h
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1212 := derived1212 a h
  have h9 : Entails.eval a c1452 := derived1452 a h
  have h10 : Entails.eval a c132 := h 131 (by decide)
  have h11 : Entails.eval a c420 := derived420 a h
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c1453 := derived1453 a h
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  have h18 : Entails.eval a c1183 := derived1183 a h
  have h19 : Entails.eval a c1454 := derived1454 a h
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c16 := h 15 (by decide)
  have h23 : Entails.eval a c17 := h 16 (by decide)
  have h24 : Entails.eval a c961 := derived961 a h
  have h25 : Entails.eval a c110 := h 109 (by decide)
  have h26 : Entails.eval a c71 := h 70 (by decide)
  have h27 : Entails.eval a c73 := h 72 (by decide)
  have h28 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1444, some c1394, some c1430, some c1212, some c1452, some c34, some c1455, some c39, some c43, some c209, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 57) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c1444, c1394, c1430, c1212, c1452, c34, c1455, c39, c43, c209] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c1444 := derived1444 a h
  have h1 : Entails.eval a c1394 := derived1394 a h
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c1212 := derived1212 a h
  have h4 : Entails.eval a c1452 := derived1452 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c1455 := derived1455 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1457 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c25, some c37, some c110, some c1230, some c288, some c1079, some c215, some c322, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 57) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c264, c25, c37, c110, c1230, c288, c1079, c215, c322] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c1230 := derived1230 a h
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c1079 := derived1079 a h
  have h7 : Entails.eval a c215 := h 214 (by decide)
  have h8 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1444, some c1456, some c264, some c35, some c6, some c25, some c1394, some c1430, some c1212, some c1452, some c160, some c204, some c58, some c141, some c188, some c99, some c1457, some c256, some c101, some c110, some c1230, some c17, some c288, some c964, some c202, some c1079, some c140, some c322, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 57) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c1444, c1456, c264, c35, c6, c25, c1394, c1430, c1212, c1452, c160, c204, c58, c141, c188, c99, c1457, c256, c101, c110, c1230, c17, c288, c964, c202, c1079, c140, c322] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c1444 := derived1444 a h
  have h1 : Entails.eval a c1456 := derived1456 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c1394 := derived1394 a h
  have h7 : Entails.eval a c1430 := derived1430 a h
  have h8 : Entails.eval a c1212 := derived1212 a h
  have h9 : Entails.eval a c1452 := derived1452 a h
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c141 := h 140 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c99 := h 98 (by decide)
  have h16 : Entails.eval a c1457 := derived1457 a h
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c101 := h 100 (by decide)
  have h19 : Entails.eval a c110 := h 109 (by decide)
  have h20 : Entails.eval a c1230 := derived1230 a h
  have h21 : Entails.eval a c17 := h 16 (by decide)
  have h22 : Entails.eval a c288 := h 287 (by decide)
  have h23 : Entails.eval a c964 := derived964 a h
  have h24 : Entails.eval a c202 := h 201 (by decide)
  have h25 : Entails.eval a c1079 := derived1079 a h
  have h26 : Entails.eval a c140 := h 139 (by decide)
  have h27 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c124, some c964, some c205, some c14, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 57) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c1430, c124, c964, c205, c14] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c964 := derived964 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1460 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1456, some c264, some c6, some c25, some c1444, some c1394, some c1430, some c1212, some c1452, some c132, some c229, some c1458, some c13, some c134, some c1459, some c202, some c140, some c14, some c46, some c110, some c1079, some c1230, some c323, some c167, some c141, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 57) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c1456, c264, c6, c25, c1444, c1394, c1430, c1212, c1452, c132, c229, c1458, c13, c134, c1459, c202, c140, c14, c46, c110, c1079, c1230, c323, c167, c141] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c1456 := derived1456 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c1444 := derived1444 a h
  have h5 : Entails.eval a c1394 := derived1394 a h
  have h6 : Entails.eval a c1430 := derived1430 a h
  have h7 : Entails.eval a c1212 := derived1212 a h
  have h8 : Entails.eval a c1452 := derived1452 a h
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c1458 := derived1458 a h
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c1459 := derived1459 a h
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c46 := h 45 (by decide)
  have h19 : Entails.eval a c110 := h 109 (by decide)
  have h20 : Entails.eval a c1079 := derived1079 a h
  have h21 : Entails.eval a c1230 := derived1230 a h
  have h22 : Entails.eval a c323 := h 322 (by decide)
  have h23 : Entails.eval a c167 := h 166 (by decide)
  have h24 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1461 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1452, some c1444, some c1430, some c1212, some c1394, some c1456, some c264, some c25, some c35, some c1460, some c39, some c1309, some c209, some c319, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 57) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c1452, c1444, c1430, c1212, c1394, c1456, c264, c25, c35, c1460, c39, c1309, c209, c319] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c1452 := derived1452 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c1212 := derived1212 a h
  have h4 : Entails.eval a c1394 := derived1394 a h
  have h5 : Entails.eval a c1456 := derived1456 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c1460 := derived1460 a h
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c1309 := derived1309 a h
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c32, some c3, some c113, some c39, some c1416, some c34, some c43, some c212, some c209, some c317, some c268, some c779, some c33, some c121, some c110, some c205, some c17, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 57) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c1430, c32, c3, c113, c39, c1416, c34, c43, c212, c209, c317, c268, c779, c33, c121, c110, c205, c17] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c1416 := derived1416 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c779 := derived779 a h
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1461, some c1452, some c1444, some c1430, some c22, some c3, some c32, some c1462, some c583, some c271, some c1230, some c1232, some c121, some c161, some c361, some c257, some c17, some c71, some c1306, some c162, some c217, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 57) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c1461, c1452, c1444, c1430, c22, c3, c32, c1462, c583, c271, c1230, c1232, c121, c161, c361, c257, c17, c71, c1306, c162, c217] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c1461 := derived1461 a h
  have h1 : Entails.eval a c1452 := derived1452 a h
  have h2 : Entails.eval a c1444 := derived1444 a h
  have h3 : Entails.eval a c1430 := derived1430 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c1462 := derived1462 a h
  have h8 : Entails.eval a c583 := derived583 a h
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c1230 := derived1230 a h
  have h11 : Entails.eval a c1232 := derived1232 a h
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c71 := h 70 (by decide)
  have h18 : Entails.eval a c1306 := derived1306 a h
  have h19 : Entails.eval a c162 := h 161 (by decide)
  have h20 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1464 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c205, some c16, some c204, some c122, some c17, some c270, some c110, some c37, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 57) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c121, c205, c16, c204, c122, c17, c270, c110, c37] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c270, some c267, some c208, some c209, some c319, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 57) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c270, c267, c208, c209, c319] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c270 := h 269 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1461, some c113, some c1452, some c39, some c1463, some c1465, some c122, some c1416, some c1444, some c1464, some c204, some c201, some c16, some c114, some c133, some c205, some c75, some c235, some c168, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 57) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c1461, c113, c1452, c39, c1463, c1465, c122, c1416, c1444, c1464, c204, c201, c16, c114, c133, c205, c75, c235, c168] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c1461 := derived1461 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c1452 := derived1452 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1463 := derived1463 a h
  have h5 : Entails.eval a c1465 := derived1465 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c1416 := derived1416 a h
  have h8 : Entails.eval a c1444 := derived1444 a h
  have h9 : Entails.eval a c1464 := derived1464 a h
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1467 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1463, some c1452, some c1461, some c113, some c39, some c1444, some c1430, some c1416, some c1465, some c1466, some c13, some c205, some c121, some c14, some c110, some c36, some c38, some c268, some c43, some c209, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 57) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c1463, c1452, c1461, c113, c39, c1444, c1430, c1416, c1465, c1466, c13, c205, c121, c14, c110, c36, c38, c268, c43, c209] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c1463 := derived1463 a h
  have h1 : Entails.eval a c1452 := derived1452 a h
  have h2 : Entails.eval a c1461 := derived1461 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c1444 := derived1444 a h
  have h6 : Entails.eval a c1430 := derived1430 a h
  have h7 : Entails.eval a c1416 := derived1416 a h
  have h8 : Entails.eval a c1465 := derived1465 a h
  have h9 : Entails.eval a c1466 := derived1466 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c114, some c143, some c267, some c319, some c122, some c779, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 57) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c113, c114, c143, c267, c319, c122, c779] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c779 := derived779 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c1464, some c1468, some c201, some c202, some c122, some c17, some c270, some c110, some c37, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 57) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c121, c1464, c1468, c201, c202, c122, c17, c270, c110, c37] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c1464 := derived1464 a h
  have h2 : Entails.eval a c1468 := derived1468 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1469, some c271, some c35, some c4, some c270, some c122, some c36, some c204, some c201, some c110, some c1468, some c18, some c205, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 57) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c1469, c271, c35, c4, c270, c122, c36, c204, c201, c110, c1468, c18, c205] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c1469 := derived1469 a h
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c1468 := derived1468 a h
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c205, some c202, some c15, some c143, some c43, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 57) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c1430, c205, c202, c15, c143, c43] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1444, some c1452, some c1461, some c113, some c39, some c1463, some c1467, some c1470, some c13, some c1471, some c121, some c14, some c271, some c110, some c35, some c36, some c270, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 57) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c1430, c1444, c1452, c1461, c113, c39, c1463, c1467, c1470, c13, c1471, c121, c14, c271, c110, c35, c36, c270] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1452 := derived1452 a h
  have h3 : Entails.eval a c1461 := derived1461 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c1463 := derived1463 a h
  have h7 : Entails.eval a c1467 := derived1467 a h
  have h8 : Entails.eval a c1470 := derived1470 a h
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c1471 := derived1471 a h
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1473 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c217, some c286, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1473 : lratChecker f1473 p1473 = .success := by decide +kernel
theorem unsat1473 : Unsatisfiable (PosFin 57) f1473 := by
  apply lratCheckerSound f1473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1473
  · intro a ha; simp [p1473] at ha; subst a; trivial
  · exact checked1473
theorem derived1473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1473 := by
  apply localUnsat_implies_entails f1473 [c206, c217, c286] c1473 unsat1473 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1474 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1472, some c553, some c3, some c1357, some c1348, some c207, some c15, some c200, some c11, some c26, some c38, some c155, some c884, some c1473, some c1029, some c203, some c1083, some c159, some c53, some c66, some c149, some c1340, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1474 : lratChecker f1474 p1474 = .success := by decide +kernel
theorem unsat1474 : Unsatisfiable (PosFin 57) f1474 := by
  apply lratCheckerSound f1474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1474
  · intro a ha; simp [p1474] at ha; subst a; trivial
  · exact checked1474
theorem derived1474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1474 := by
  apply localUnsat_implies_entails f1474 [c1430, c1472, c553, c3, c1357, c1348, c207, c15, c200, c11, c26, c38, c155, c884, c1473, c1029, c203, c1083, c159, c53, c66, c149, c1340] c1474 unsat1474 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1472 := derived1472 a h
  have h2 : Entails.eval a c553 := derived553 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1348 := derived1348 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c884 := derived884 a h
  have h14 : Entails.eval a c1473 := derived1473 a h
  have h15 : Entails.eval a c1029 := derived1029 a h
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c1083 := derived1083 a h
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c66 := h 65 (by decide)
  have h21 : Entails.eval a c149 := h 148 (by decide)
  have h22 : Entails.eval a c1340 := derived1340 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1475 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1472, some c553, some c1430, some c106, some c15, some c200, some c11, some c6, some c1330, some c3, some c1357, some c1348, some c207, some c1474, some c1442, some c61, some c94, some c1340, some c179, some c137, some c237, some c172, some c77, some c1237, some c341, some c218, some c357, some c1329, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1475 : lratChecker f1475 p1475 = .success := by decide +kernel
theorem unsat1475 : Unsatisfiable (PosFin 57) f1475 := by
  apply lratCheckerSound f1475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1475
  · intro a ha; simp [p1475] at ha; subst a; trivial
  · exact checked1475
theorem derived1475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1475 := by
  apply localUnsat_implies_entails f1475 [c1472, c553, c1430, c106, c15, c200, c11, c6, c1330, c3, c1357, c1348, c207, c1474, c1442, c61, c94, c1340, c179, c137, c237, c172, c77, c1237, c341, c218, c357, c1329] c1475 unsat1475 (by rfl) a
  have h0 : Entails.eval a c1472 := derived1472 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c1330 := derived1330 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1357 := derived1357 a h
  have h11 : Entails.eval a c1348 := derived1348 a h
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c1474 := derived1474 a h
  have h14 : Entails.eval a c1442 := derived1442 a h
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c1340 := derived1340 a h
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c172 := h 171 (by decide)
  have h22 : Entails.eval a c77 := h 76 (by decide)
  have h23 : Entails.eval a c1237 := derived1237 a h
  have h24 : Entails.eval a c341 := h 340 (by decide)
  have h25 : Entails.eval a c218 := h 217 (by decide)
  have h26 : Entails.eval a c357 := h 356 (by decide)
  have h27 : Entails.eval a c1329 := derived1329 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1476 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1472, some c553, some c1430, some c106, some c1330, some c15, some c200, some c1475, some c41, some c144, some c147, some c317, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1476 : lratChecker f1476 p1476 = .success := by decide +kernel
theorem unsat1476 : Unsatisfiable (PosFin 57) f1476 := by
  apply lratCheckerSound f1476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1476
  · intro a ha; simp [p1476] at ha; subst a; trivial
  · exact checked1476
theorem derived1476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1476 := by
  apply localUnsat_implies_entails f1476 [c1472, c553, c1430, c106, c1330, c15, c200, c1475, c41, c144, c147, c317] c1476 unsat1476 (by rfl) a
  have h0 : Entails.eval a c1472 := derived1472 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1330 := derived1330 a h
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c1475 := derived1475 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1477 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c553, some c13, some c197, some c2, some c11, some c1418, some c15, some c3, some c1357, some c1348, some c119, some c131, some c1419, some c268, some c23, some c35, some c153, some c218, some c167, some c61, some c66, some c254, some c358, some c58, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1477 : lratChecker f1477 p1477 = .success := by decide +kernel
theorem unsat1477 : Unsatisfiable (PosFin 57) f1477 := by
  apply lratCheckerSound f1477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1477
  · intro a ha; simp [p1477] at ha; subst a; trivial
  · exact checked1477
theorem derived1477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1477 := by
  apply localUnsat_implies_entails f1477 [c553, c13, c197, c2, c11, c1418, c15, c3, c1357, c1348, c119, c131, c1419, c268, c23, c35, c153, c218, c167, c61, c66, c254, c358, c58] c1477 unsat1477 (by rfl) a
  have h0 : Entails.eval a c553 := derived553 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c1418 := derived1418 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c1357 := derived1357 a h
  have h9 : Entails.eval a c1348 := derived1348 a h
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c1419 := derived1419 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c167 := h 166 (by decide)
  have h19 : Entails.eval a c61 := h 60 (by decide)
  have h20 : Entails.eval a c66 := h 65 (by decide)
  have h21 : Entails.eval a c254 := h 253 (by decide)
  have h22 : Entails.eval a c358 := h 357 (by decide)
  have h23 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1478 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c207, some c1407, some c154, some c218, some c1473, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1478 : lratChecker f1478 p1478 = .success := by decide +kernel
theorem unsat1478 : Unsatisfiable (PosFin 57) f1478 := by
  apply lratCheckerSound f1478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1478
  · intro a ha; simp [p1478] at ha; subst a; trivial
  · exact checked1478
theorem derived1478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1478 := by
  apply localUnsat_implies_entails f1478 [c207, c1407, c154, c218, c1473] c1478 unsat1478 (by rfl) a
  have h0 : Entails.eval a c207 := h 206 (by decide)
  have h1 : Entails.eval a c1407 := derived1407 a h
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c218 := h 217 (by decide)
  have h4 : Entails.eval a c1473 := derived1473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1479 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨41, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1418, some c553, some c3, some c13, some c197, some c2, some c415, some c11, some c1357, some c1348, some c207, some c1477, some c1478, some c271, some c241, some c23, some c36, some c289, some c153, some c53, some c218, some c1277, some c69, some c73, some c361, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1479 : lratChecker f1479 p1479 = .success := by decide +kernel
theorem unsat1479 : Unsatisfiable (PosFin 57) f1479 := by
  apply lratCheckerSound f1479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1479
  · intro a ha; simp [p1479] at ha; subst a; trivial
  · exact checked1479
theorem derived1479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1479 := by
  apply localUnsat_implies_entails f1479 [c1418, c553, c3, c13, c197, c2, c415, c11, c1357, c1348, c207, c1477, c1478, c271, c241, c23, c36, c289, c153, c53, c218, c1277, c69, c73, c361] c1479 unsat1479 (by rfl) a
  have h0 : Entails.eval a c1418 := derived1418 a h
  have h1 : Entails.eval a c553 := derived553 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c415 := derived415 a h
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c1357 := derived1357 a h
  have h9 : Entails.eval a c1348 := derived1348 a h
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c1477 := derived1477 a h
  have h12 : Entails.eval a c1478 := derived1478 a h
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c289 := h 288 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c1277 := derived1277 a h
  have h22 : Entails.eval a c69 := h 68 (by decide)
  have h23 : Entails.eval a c73 := h 72 (by decide)
  have h24 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1480 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1472, some c1430, some c553, some c3, some c1476, some c1418, some c13, some c15, some c197, some c2, some c415, some c79, some c1479, some c43, some c143, some c146, some c315, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1480 : lratChecker f1480 p1480 = .success := by decide +kernel
theorem unsat1480 : Unsatisfiable (PosFin 57) f1480 := by
  apply lratCheckerSound f1480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1480
  · intro a ha; simp [p1480] at ha; subst a; trivial
  · exact checked1480
theorem derived1480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1480 := by
  apply localUnsat_implies_entails f1480 [c1472, c1430, c553, c3, c1476, c1418, c13, c15, c197, c2, c415, c79, c1479, c43, c143, c146, c315] c1480 unsat1480 (by rfl) a
  have h0 : Entails.eval a c1472 := derived1472 a h
  have h1 : Entails.eval a c1430 := derived1430 a h
  have h2 : Entails.eval a c553 := derived553 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1476 := derived1476 a h
  have h5 : Entails.eval a c1418 := derived1418 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c415 := derived415 a h
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c1479 := derived1479 a h
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c143 := h 142 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1481 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c197, some c13, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1481 : lratChecker f1481 p1481 = .success := by decide +kernel
theorem unsat1481 : Unsatisfiable (PosFin 57) f1481 := by
  apply lratCheckerSound f1481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1481
  · intro a ha; simp [p1481] at ha; subst a; trivial
  · exact checked1481
theorem derived1481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1481 := by
  apply localUnsat_implies_entails f1481 [c196, c197, c13] c1481 unsat1481 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1482 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1212, some c1394, some c124, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1482 : lratChecker f1482 p1482 = .success := by decide +kernel
theorem unsat1482 : Unsatisfiable (PosFin 57) f1482 := by
  apply lratCheckerSound f1482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1482
  · intro a ha; simp [p1482] at ha; subst a; trivial
  · exact checked1482
theorem derived1482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1482 := by
  apply localUnsat_implies_entails f1482 [c1212, c1394, c124] c1482 unsat1482 (by rfl) a
  have h0 : Entails.eval a c1212 := derived1212 a h
  have h1 : Entails.eval a c1394 := derived1394 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1483 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c119, some c124, some c268, some c33, some c206, some c52, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1483 : lratChecker f1483 p1483 = .success := by decide +kernel
theorem unsat1483 : Unsatisfiable (PosFin 57) f1483 := by
  apply lratCheckerSound f1483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1483
  · intro a ha; simp [p1483] at ha; subst a; trivial
  · exact checked1483
theorem derived1483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1483 := by
  apply localUnsat_implies_entails f1483 [c7, c119, c124, c268, c33, c206, c52] c1483 unsat1483 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1484 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1480, some c104, some c1472, some c1418, some c1481, some c1482, some c22, some c3, some c32, some c152, some c1483, some c583, some c271, some c1230, some c33, some c206, some c161, some c1473, some c19, some c150, some c52, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1484 : lratChecker f1484 p1484 = .success := by decide +kernel
theorem unsat1484 : Unsatisfiable (PosFin 57) f1484 := by
  apply lratCheckerSound f1484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1484
  · intro a ha; simp [p1484] at ha; subst a; trivial
  · exact checked1484
theorem derived1484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1484 := by
  apply localUnsat_implies_entails f1484 [c1430, c1480, c104, c1472, c1418, c1481, c1482, c22, c3, c32, c152, c1483, c583, c271, c1230, c33, c206, c161, c1473, c19, c150, c52] c1484 unsat1484 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1480 := derived1480 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c1472 := derived1472 a h
  have h4 : Entails.eval a c1418 := derived1418 a h
  have h5 : Entails.eval a c1481 := derived1481 a h
  have h6 : Entails.eval a c1482 := derived1482 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c1483 := derived1483 a h
  have h12 : Entails.eval a c583 := derived583 a h
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c1230 := derived1230 a h
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c1473 := derived1473 a h
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1485 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1484, some c1430, some c1480, some c104, some c1472, some c1418, some c1481, some c1482, some c7, some c119, some c124, some c267, some c131, some c207, some c1419, some c268, some c23, some c4, some c36, some c153, some c110, some c47, some c218, some c133, some c75, some c235, some c289, some c286, some c69, some c73, some c361, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1485 : lratChecker f1485 p1485 = .success := by decide +kernel
theorem unsat1485 : Unsatisfiable (PosFin 57) f1485 := by
  apply lratCheckerSound f1485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1485
  · intro a ha; simp [p1485] at ha; subst a; trivial
  · exact checked1485
theorem derived1485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1485 := by
  apply localUnsat_implies_entails f1485 [c1484, c1430, c1480, c104, c1472, c1418, c1481, c1482, c7, c119, c124, c267, c131, c207, c1419, c268, c23, c4, c36, c153, c110, c47, c218, c133, c75, c235, c289, c286, c69, c73, c361] c1485 unsat1485 (by rfl) a
  have h0 : Entails.eval a c1484 := derived1484 a h
  have h1 : Entails.eval a c1430 := derived1430 a h
  have h2 : Entails.eval a c1480 := derived1480 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1472 := derived1472 a h
  have h5 : Entails.eval a c1418 := derived1418 a h
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c1482 := derived1482 a h
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c131 := h 130 (by decide)
  have h13 : Entails.eval a c207 := h 206 (by decide)
  have h14 : Entails.eval a c1419 := derived1419 a h
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c218 := h 217 (by decide)
  have h23 : Entails.eval a c133 := h 132 (by decide)
  have h24 : Entails.eval a c75 := h 74 (by decide)
  have h25 : Entails.eval a c235 := h 234 (by decide)
  have h26 : Entails.eval a c289 := h 288 (by decide)
  have h27 : Entails.eval a c286 := h 285 (by decide)
  have h28 : Entails.eval a c69 := h 68 (by decide)
  have h29 : Entails.eval a c73 := h 72 (by decide)
  have h30 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1486 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c207, some c206, some c322, some c133, some c143, some c114, some c560, some c233, some c324, some c323, some c293, some c234, some c1406, some c36, some c5, some c110, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1486 : lratChecker f1486 p1486 = .success := by decide +kernel
theorem unsat1486 : Unsatisfiable (PosFin 57) f1486 := by
  apply lratCheckerSound f1486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1486
  · intro a ha; simp [p1486] at ha; subst a; trivial
  · exact checked1486
theorem derived1486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1486 := by
  apply localUnsat_implies_entails f1486 [c207, c206, c322, c133, c143, c114, c560, c233, c324, c323, c293, c234, c1406, c36, c5, c110] c1486 unsat1486 (by rfl) a
  have h0 : Entails.eval a c207 := h 206 (by decide)
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c322 := h 321 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c560 := derived560 a h
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c293 := h 292 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c1406 := derived1406 a h
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c5 := h 4 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1487 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1418, some c198, some c6, some c16, some c270, some c207, some c1486, some c271, some c23, some c36, some c153, some c110, some c47, some c218, some c18, some c560, some c288, some c435, some c73, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1487 : lratChecker f1487 p1487 = .success := by decide +kernel
theorem unsat1487 : Unsatisfiable (PosFin 57) f1487 := by
  apply lratCheckerSound f1487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1487
  · intro a ha; simp [p1487] at ha; subst a; trivial
  · exact checked1487
theorem derived1487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1487 := by
  apply localUnsat_implies_entails f1487 [c1418, c198, c6, c16, c270, c207, c1486, c271, c23, c36, c153, c110, c47, c218, c18, c560, c288, c435, c73] c1487 unsat1487 (by rfl) a
  have h0 : Entails.eval a c1418 := derived1418 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c1486 := derived1486 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c560 := derived560 a h
  have h16 : Entails.eval a c288 := h 287 (by decide)
  have h17 : Entails.eval a c435 := derived435 a h
  have h18 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1488 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c270, some c267, some c37, some c114, some c46, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1488 : lratChecker f1488 p1488 = .success := by decide +kernel
theorem unsat1488 : Unsatisfiable (PosFin 57) f1488 := by
  apply lratCheckerSound f1488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1488
  · intro a ha; simp [p1488] at ha; subst a; trivial
  · exact checked1488
theorem derived1488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1488 := by
  apply localUnsat_implies_entails f1488 [c270, c267, c37, c114, c46] c1488 unsat1488 (by rfl) a
  have h0 : Entails.eval a c270 := h 269 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1489 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c1482, some c206, some c1488, some c207, some c322, some c143, some c52, some c24, some c1277, some c286, some c285, some c71, some c218, some c1329, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1489 : lratChecker f1489 p1489 = .success := by decide +kernel
theorem unsat1489 : Unsatisfiable (PosFin 57) f1489 := by
  apply lratCheckerSound f1489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1489
  · intro a ha; simp [p1489] at ha; subst a; trivial
  · exact checked1489
theorem derived1489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1489 := by
  apply localUnsat_implies_entails f1489 [c15, c1482, c206, c1488, c207, c322, c143, c52, c24, c1277, c286, c285, c71, c218, c1329] c1489 unsat1489 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c1482 := derived1482 a h
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c1488 := derived1488 a h
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c1277 := derived1277 a h
  have h10 : Entails.eval a c286 := h 285 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c1329 := derived1329 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1490 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1480, some c104, some c1472, some c1418, some c1481, some c1482, some c1484, some c1485, some c1487, some c13, some c1489, some c271, some c23, some c35, some c153, some c270, some c218, some c36, some c110, some c1277, some c69, some c73, some c361, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1490 : lratChecker f1490 p1490 = .success := by decide +kernel
theorem unsat1490 : Unsatisfiable (PosFin 57) f1490 := by
  apply lratCheckerSound f1490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1490
  · intro a ha; simp [p1490] at ha; subst a; trivial
  · exact checked1490
theorem derived1490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1490 := by
  apply localUnsat_implies_entails f1490 [c1430, c1480, c104, c1472, c1418, c1481, c1482, c1484, c1485, c1487, c13, c1489, c271, c23, c35, c153, c270, c218, c36, c110, c1277, c69, c73, c361] c1490 unsat1490 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1480 := derived1480 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c1472 := derived1472 a h
  have h4 : Entails.eval a c1418 := derived1418 a h
  have h5 : Entails.eval a c1481 := derived1481 a h
  have h6 : Entails.eval a c1482 := derived1482 a h
  have h7 : Entails.eval a c1484 := derived1484 a h
  have h8 : Entails.eval a c1485 := derived1485 a h
  have h9 : Entails.eval a c1487 := derived1487 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c1489 := derived1489 a h
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c110 := h 109 (by decide)
  have h20 : Entails.eval a c1277 := derived1277 a h
  have h21 : Entails.eval a c69 := h 68 (by decide)
  have h22 : Entails.eval a c73 := h 72 (by decide)
  have h23 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1491 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1472, some c1480, some c104, some c1418, some c1481, some c1490, some c39, some c143, some c43, some c319, some c15, some c560, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1491 : lratChecker f1491 p1491 = .success := by decide +kernel
theorem unsat1491 : Unsatisfiable (PosFin 57) f1491 := by
  apply lratCheckerSound f1491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1491
  · intro a ha; simp [p1491] at ha; subst a; trivial
  · exact checked1491
theorem derived1491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1491 := by
  apply localUnsat_implies_entails f1491 [c1430, c1472, c1480, c104, c1418, c1481, c1490, c39, c143, c43, c319, c15, c560] c1491 unsat1491 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1472 := derived1472 a h
  have h2 : Entails.eval a c1480 := derived1480 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1418 := derived1418 a h
  have h5 : Entails.eval a c1481 := derived1481 a h
  have h6 : Entails.eval a c1490 := derived1490 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c560 := derived560 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1492 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨46, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c2, some c228, some c133, some c170, some c204, some c141, some c320, some c322, some c211, some c140, some c269, some c205, some c129, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1492 : lratChecker f1492 p1492 = .success := by decide +kernel
theorem unsat1492 : Unsatisfiable (PosFin 57) f1492 := by
  apply lratCheckerSound f1492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1492
  · intro a ha; simp [p1492] at ha; subst a; trivial
  · exact checked1492
theorem derived1492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1492 := by
  apply localUnsat_implies_entails f1492 [c132, c2, c228, c133, c170, c204, c141, c320, c322, c211, c140, c269, c205, c129] c1492 unsat1492 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1493 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨39, by decide⟩, false), (⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1491, some c107, some c1430, some c1434, some c163, some c130, some c224, some c961, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 57) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c1491, c107, c1430, c1434, c163, c130, c224, c961] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c1491 := derived1491 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c1434 := derived1434 a h
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c130 := h 129 (by decide)
  have h6 : Entails.eval a c224 := h 223 (by decide)
  have h7 : Entails.eval a c961 := derived961 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1493

end CochromaticTwenty.Certificates.B16_0_0
