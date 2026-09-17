import MerLeanExperiment.Certificates.B16_8_0Enumerating.Steps0900_0999

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1419 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1418, some c65, some c368, some c80, some c315, some c35, some c271, some c268, some c45, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 57) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c1405, c1049, c1418, c65, c368, c80, c315, c35, c271, c268, c45] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1418 := derived1418 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1418, some c65, some c1416, some c772, some c1419, some c75, some c315, some c35, some c271, some c45, some c50, some c291, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 57) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c1405, c1049, c1418, c65, c1416, c772, c1419, c75, c315, c35, c271, c45, c50, c291] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1418 := derived1418 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c1416 := derived1416 a h
  have h5 : Entails.eval a c772 := derived772 a h
  have h6 : Entails.eval a c1419 := derived1419 a h
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1418, some c1416, some c1405, some c1049, some c1420, some c103, some c85, some c683, some c475, some c36, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 57) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c1418, c1416, c1405, c1049, c1420, c103, c85, c683, c475, c36] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c1418 := derived1418 a h
  have h1 : Entails.eval a c1416 := derived1416 a h
  have h2 : Entails.eval a c1405 := derived1405 a h
  have h3 : Entails.eval a c1049 := derived1049 a h
  have h4 : Entails.eval a c1420 := derived1420 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c683 := derived683 a h
  have h8 : Entails.eval a c475 := derived475 a h
  have h9 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1418, some c65, some c1421, some c68, some c368, some c75, some c1025, some c541, some c35, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 57) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c1405, c1049, c1418, c65, c1421, c68, c368, c75, c1025, c541, c35] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1418 := derived1418 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c1421 := derived1421 a h
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c1025 := derived1025 a h
  have h9 : Entails.eval a c541 := derived541 a h
  have h10 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1416, some c1418, some c65, some c1421, some c68, some c1422, some c103, some c92, some c447, some c683, some c293, some c36, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 57) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c1405, c1049, c1416, c1418, c65, c1421, c68, c1422, c103, c92, c447, c683, c293, c36] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1416 := derived1416 a h
  have h3 : Entails.eval a c1418 := derived1418 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c1421 := derived1421 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c1422 := derived1422 a h
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c447 := derived447 a h
  have h11 : Entails.eval a c683 := derived683 a h
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c965, some c863, some c35, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 57) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1405, c1049, c965, c863, c35] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c965 := derived965 a h
  have h3 : Entails.eval a c863 := derived863 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c328, some c40, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 57) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c284, c328, c40] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c1405, some c1049, some c1097, some c1135, some c380, some c359, some c1424, some c358, some c371, some c1425, some c74, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 57) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c1423, c100, c1282, c1405, c1049, c1097, c1135, c380, c359, c1424, c358, c371, c1425, c74] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1405 := derived1405 a h
  have h4 : Entails.eval a c1049 := derived1049 a h
  have h5 : Entails.eval a c1097 := derived1097 a h
  have h6 : Entails.eval a c1135 := derived1135 a h
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c1424 := derived1424 a h
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c1425 := derived1425 a h
  have h13 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c1405, some c1049, some c65, some c85, some c813, some c1077, some c359, some c371, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 57) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c1423, c100, c1282, c1405, c1049, c65, c85, c813, c1077, c359, c371] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1405 := derived1405 a h
  have h4 : Entails.eval a c1049 := derived1049 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c1077 := derived1077 a h
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1428 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1405, some c92, some c91, some c905, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 57) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c1423, c100, c1405, c92, c91, c905] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1405 := derived1405 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c905 := derived905 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1428, some c1427, some c1426, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 57) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c1428, c1427, c1426] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1427 := derived1427 a h
  have h2 : Entails.eval a c1426 := derived1426 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1405, some c1049, some c1428, some c1429, some c378, some c65, some c85, some c813, some c1077, some c382, some c371, some c1394, some c362, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 57) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c1423, c100, c1405, c1049, c1428, c1429, c378, c65, c85, c813, c1077, c382, c371, c1394, c362] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1405 := derived1405 a h
  have h3 : Entails.eval a c1049 := derived1049 a h
  have h4 : Entails.eval a c1428 := derived1428 a h
  have h5 : Entails.eval a c1429 := derived1429 a h
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c1077 := derived1077 a h
  have h11 : Entails.eval a c382 := h 381 (by decide)
  have h12 : Entails.eval a c371 := h 370 (by decide)
  have h13 : Entails.eval a c1394 := derived1394 a h
  have h14 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨27, by decide⟩, true), (⟨35, by decide⟩, true), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c326, some c282, some c262, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 57) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c326, c282, c262] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c326 := h 325 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c1081, some c380, some c358, some c379, some c172, some c148, some c445, some c1405, some c1049, some c1135, some c1097, some c1430, some c72, some c94, some c322, some c278, some c16, some c1431, some c164, some c1278, some c1273, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 57) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c1423, c100, c1282, c1081, c380, c358, c379, c172, c148, c445, c1405, c1049, c1135, c1097, c1430, c72, c94, c322, c278, c16, c1431, c164, c1278, c1273] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1081 := derived1081 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c445 := derived445 a h
  have h10 : Entails.eval a c1405 := derived1405 a h
  have h11 : Entails.eval a c1049 := derived1049 a h
  have h12 : Entails.eval a c1135 := derived1135 a h
  have h13 : Entails.eval a c1097 := derived1097 a h
  have h14 : Entails.eval a c1430 := derived1430 a h
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c322 := h 321 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  have h19 : Entails.eval a c16 := h 15 (by decide)
  have h20 : Entails.eval a c1431 := derived1431 a h
  have h21 : Entails.eval a c164 := h 163 (by decide)
  have h22 : Entails.eval a c1278 := derived1278 a h
  have h23 : Entails.eval a c1273 := derived1273 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c380, some c359, some c1405, some c1049, some c1135, some c1097, some c148, some c1430, some c358, some c379, some c445, some c1432, some c301, some c1089, some c81, some c278, some c1186, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 57) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c1423, c100, c1282, c380, c359, c1405, c1049, c1135, c1097, c148, c1430, c358, c379, c445, c1432, c301, c1089, c81, c278, c1186] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c1405 := derived1405 a h
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c1135 := derived1135 a h
  have h8 : Entails.eval a c1097 := derived1097 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1430 := derived1430 a h
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c445 := derived445 a h
  have h14 : Entails.eval a c1432 := derived1432 a h
  have h15 : Entails.eval a c301 := h 300 (by decide)
  have h16 : Entails.eval a c1089 := derived1089 a h
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  have h19 : Entails.eval a c1186 := derived1186 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨38, by decide⟩, true), (⟨30, by decide⟩, true), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c326, some c282, some c266, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 57) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c326, c282, c266] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c326 := h 325 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c1081, some c1430, some c1405, some c1049, some c1097, some c1135, some c380, some c359, some c1433, some c371, some c1394, some c74, some c149, some c284, some c328, some c379, some c623, some c1434, some c1273, some c160, some c1278, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 57) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c1423, c100, c1282, c1081, c1430, c1405, c1049, c1097, c1135, c380, c359, c1433, c371, c1394, c74, c149, c284, c328, c379, c623, c1434, c1273, c160, c1278] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1081 := derived1081 a h
  have h4 : Entails.eval a c1430 := derived1430 a h
  have h5 : Entails.eval a c1405 := derived1405 a h
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c1097 := derived1097 a h
  have h8 : Entails.eval a c1135 := derived1135 a h
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c1433 := derived1433 a h
  have h12 : Entails.eval a c371 := h 370 (by decide)
  have h13 : Entails.eval a c1394 := derived1394 a h
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c284 := h 283 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c379 := h 378 (by decide)
  have h19 : Entails.eval a c623 := derived623 a h
  have h20 : Entails.eval a c1434 := derived1434 a h
  have h21 : Entails.eval a c1273 := derived1273 a h
  have h22 : Entails.eval a c160 := h 159 (by decide)
  have h23 : Entails.eval a c1278 := derived1278 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c1405, some c1049, some c65, some c85, some c1187, some c813, some c81, some c1185, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 57) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c1423, c100, c1282, c1405, c1049, c65, c85, c1187, c813, c81, c1185] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1405 := derived1405 a h
  have h4 : Entails.eval a c1049 := derived1049 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c1187 := derived1187 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c1185 := derived1185 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c100, some c1282, some c1405, some c1049, some c1081, some c148, some c1436, some c1435, some c68, some c92, some c813, some c359, some c1185, some c834, some c1164, some c74, some c8, some c1088, some c160, some c379, some c375, some c358, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 57) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1423, c100, c1282, c1405, c1049, c1081, c148, c1436, c1435, c68, c92, c813, c359, c1185, c834, c1164, c74, c8, c1088, c160, c379, c375, c358] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1405 := derived1405 a h
  have h4 : Entails.eval a c1049 := derived1049 a h
  have h5 : Entails.eval a c1081 := derived1081 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c1436 := derived1436 a h
  have h8 : Entails.eval a c1435 := derived1435 a h
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c813 := derived813 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c1185 := derived1185 a h
  have h14 : Entails.eval a c834 := derived834 a h
  have h15 : Entails.eval a c1164 := derived1164 a h
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c8 := h 7 (by decide)
  have h18 : Entails.eval a c1088 := derived1088 a h
  have h19 : Entails.eval a c160 := h 159 (by decide)
  have h20 : Entails.eval a c379 := h 378 (by decide)
  have h21 : Entails.eval a c375 := h 374 (by decide)
  have h22 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1438 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c873, some c109, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 57) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c873, c109] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c873 := derived873 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1439 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1437, some c1430, some c1423, some c100, some c1405, some c1049, some c378, some c383, some c65, some c85, some c84, some c813, some c683, some c475, some c382, some c188, some c454, some c240, some c23, some c1438, some c10, some c1396, some c455, some c371, some c362, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 57) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c1437, c1430, c1423, c100, c1405, c1049, c378, c383, c65, c85, c84, c813, c683, c475, c382, c188, c454, c240, c23, c1438, c10, c1396, c455, c371, c362] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c1437 := derived1437 a h
  have h1 : Entails.eval a c1430 := derived1430 a h
  have h2 : Entails.eval a c1423 := derived1423 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1405 := derived1405 a h
  have h5 : Entails.eval a c1049 := derived1049 a h
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c813 := derived813 a h
  have h12 : Entails.eval a c683 := derived683 a h
  have h13 : Entails.eval a c475 := derived475 a h
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c454 := derived454 a h
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c23 := h 22 (by decide)
  have h19 : Entails.eval a c1438 := derived1438 a h
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c1396 := derived1396 a h
  have h22 : Entails.eval a c455 := derived455 a h
  have h23 : Entails.eval a c371 := h 370 (by decide)
  have h24 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1049, some c1423, some c100, some c1282, some c1437, some c1439, some c92, some c813, some c384, some c382, some c1078, some c1394, some c1076, some c361, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 57) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c1049, c1423, c100, c1282, c1437, c1439, c92, c813, c384, c382, c1078, c1394, c1076, c361] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c1049 := derived1049 a h
  have h1 : Entails.eval a c1423 := derived1423 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1437 := derived1437 a h
  have h5 : Entails.eval a c1439 := derived1439 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c384 := h 383 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c1078 := derived1078 a h
  have h11 : Entails.eval a c1394 := derived1394 a h
  have h12 : Entails.eval a c1076 := derived1076 a h
  have h13 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1440, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 57) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1405, c1440] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1442 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c66, some c947, some c275, some c273, some c48, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 57) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c1441, c66, c947, c275, c273, c48] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c947 := derived947 a h
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1443 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨18, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨56, by decide⟩, true), (⟨8, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c954, some c374, some c209, some c366, some c325, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 57) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c954, c374, c209, c366, c325] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c954 := derived954 a h
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1444 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c944, some c1077, some c70, some c82, some c379, some c1369, some c834, some c67, some c90, some c89, some c340, some c1368, some c190, some c30, some c236, some c245, some c1442, some c24, some c1443, some c148, some c359, some c7, some c325, some c162, some c1387, some c209, some c179, some c138, some c1367, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 57) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c1441, c380, c944, c1077, c70, c82, c379, c1369, c834, c67, c90, c89, c340, c1368, c190, c30, c236, c245, c1442, c24, c1443, c148, c359, c7, c325, c162, c1387, c209, c179, c138, c1367] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c944 := derived944 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c1369 := derived1369 a h
  have h8 : Entails.eval a c834 := derived834 a h
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c340 := h 339 (by decide)
  have h13 : Entails.eval a c1368 := derived1368 a h
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c236 := h 235 (by decide)
  have h17 : Entails.eval a c245 := h 244 (by decide)
  have h18 : Entails.eval a c1442 := derived1442 a h
  have h19 : Entails.eval a c24 := h 23 (by decide)
  have h20 : Entails.eval a c1443 := derived1443 a h
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c359 := h 358 (by decide)
  have h23 : Entails.eval a c7 := h 6 (by decide)
  have h24 : Entails.eval a c325 := h 324 (by decide)
  have h25 : Entails.eval a c162 := h 161 (by decide)
  have h26 : Entails.eval a c1387 := derived1387 a h
  have h27 : Entails.eval a c209 := h 208 (by decide)
  have h28 : Entails.eval a c179 := h 178 (by decide)
  have h29 : Entails.eval a c138 := h 137 (by decide)
  have h30 : Entails.eval a c1367 := derived1367 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1445 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c66, some c86, some c860, some c379, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 57) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c1441, c66, c86, c860, c379] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c860 := derived860 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c369, some c73, some c954, some c380, some c375, some c366, some c90, some c89, some c1254, some c1368, some c190, some c30, some c24, some c1443, some c209, some c63, some c327, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 57) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c1441, c369, c73, c954, c380, c375, c366, c90, c89, c1254, c1368, c190, c30, c24, c1443, c209, c63, c327] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c954 := derived954 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c1254 := derived1254 a h
  have h10 : Entails.eval a c1368 := derived1368 a h
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c1443 := derived1443 a h
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c369, some c73, some c954, some c1446, some c379, some c569, some c93, some c296, some c275, some c1254, some c190, some c188, some c24, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 57) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1441, c369, c73, c954, c1446, c379, c569, c93, c296, c275, c1254, c190, c188, c24] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c954 := derived954 a h
  have h4 : Entails.eval a c1446 := derived1446 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c569 := derived569 a h
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c296 := h 295 (by decide)
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c1254 := derived1254 a h
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1444, some c1445, some c380, some c944, some c1447, some c1241, some c67, some c834, some c374, some c379, some c569, some c154, some c93, some c296, some c9, some c1254, some c190, some c168, some c819, some c1367, some c185, some c823, some c159, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 57) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c1441, c1444, c1445, c380, c944, c1447, c1241, c67, c834, c374, c379, c569, c154, c93, c296, c9, c1254, c190, c168, c819, c1367, c185, c823, c159] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1445 := derived1445 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c944 := derived944 a h
  have h5 : Entails.eval a c1447 := derived1447 a h
  have h6 : Entails.eval a c1241 := derived1241 a h
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c834 := derived834 a h
  have h9 : Entails.eval a c374 := h 373 (by decide)
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c569 := derived569 a h
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c1254 := derived1254 a h
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c819 := derived819 a h
  have h20 : Entails.eval a c1367 := derived1367 a h
  have h21 : Entails.eval a c185 := h 184 (by decide)
  have h22 : Entails.eval a c823 := derived823 a h
  have h23 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨18, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c369, some c73, some c954, some c188, some c275, some c273, some c48, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 57) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c1441, c369, c73, c954, c188, c275, c273, c48] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c954 := derived954 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c275 := h 274 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1444, some c1445, some c380, some c944, some c1448, some c905, some c93, some c1254, some c1368, some c190, some c24, some c1449, some c67, some c562, some c265, some c339, some c343, some c59, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 57) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c1441, c1444, c1445, c380, c944, c1448, c905, c93, c1254, c1368, c190, c24, c1449, c67, c562, c265, c339, c343, c59] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1445 := derived1445 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c944 := derived944 a h
  have h5 : Entails.eval a c1448 := derived1448 a h
  have h6 : Entails.eval a c905 := derived905 a h
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c1254 := derived1254 a h
  have h9 : Entails.eval a c1368 := derived1368 a h
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c1449 := derived1449 a h
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c562 := derived562 a h
  have h15 : Entails.eval a c265 := h 264 (by decide)
  have h16 : Entails.eval a c339 := h 338 (by decide)
  have h17 : Entails.eval a c343 := h 342 (by decide)
  have h18 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c944, some c1444, some c1445, some c1450, some c148, some c359, some c7, some c9, some c371, some c1164, some c163, some c73, some c970, some c375, some c67, some c379, some c569, some c93, some c296, some c1254, some c265, some c326, some c328, some c63, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 57) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c1441, c380, c944, c1444, c1445, c1450, c148, c359, c7, c9, c371, c1164, c163, c73, c970, c375, c67, c379, c569, c93, c296, c1254, c265, c326, c328, c63] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c944 := derived944 a h
  have h3 : Entails.eval a c1444 := derived1444 a h
  have h4 : Entails.eval a c1445 := derived1445 a h
  have h5 : Entails.eval a c1450 := derived1450 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c1164 := derived1164 a h
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c970 := derived970 a h
  have h15 : Entails.eval a c375 := h 374 (by decide)
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c379 := h 378 (by decide)
  have h18 : Entails.eval a c569 := derived569 a h
  have h19 : Entails.eval a c93 := h 92 (by decide)
  have h20 : Entails.eval a c296 := h 295 (by decide)
  have h21 : Entails.eval a c1254 := derived1254 a h
  have h22 : Entails.eval a c265 := h 264 (by decide)
  have h23 : Entails.eval a c326 := h 325 (by decide)
  have h24 : Entails.eval a c328 := h 327 (by decide)
  have h25 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c66, some c367, some c73, some c1442, some c191, some c59, some c275, some c317, some c36, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 57) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1441, c66, c367, c73, c1442, c191, c59, c275, c317, c36] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c1442 := derived1442 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c66, some c87, some c964, some c1254, some c1368, some c190, some c236, some c245, some c1452, some c67, some c78, some c379, some c569, some c834, some c374, some c1239, some c152, some c275, some c169, some c17, some c36, some c163, some c703, some c178, some c156, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 57) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c1441, c380, c66, c87, c964, c1254, c1368, c190, c236, c245, c1452, c67, c78, c379, c569, c834, c374, c1239, c152, c275, c169, c17, c36, c163, c703, c178, c156] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c964 := derived964 a h
  have h5 : Entails.eval a c1254 := derived1254 a h
  have h6 : Entails.eval a c1368 := derived1368 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c1452 := derived1452 a h
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c569 := derived569 a h
  have h15 : Entails.eval a c834 := derived834 a h
  have h16 : Entails.eval a c374 := h 373 (by decide)
  have h17 : Entails.eval a c1239 := derived1239 a h
  have h18 : Entails.eval a c152 := h 151 (by decide)
  have h19 : Entails.eval a c275 := h 274 (by decide)
  have h20 : Entails.eval a c169 := h 168 (by decide)
  have h21 : Entails.eval a c17 := h 16 (by decide)
  have h22 : Entails.eval a c36 := h 35 (by decide)
  have h23 : Entails.eval a c163 := h 162 (by decide)
  have h24 : Entails.eval a c703 := derived703 a h
  have h25 : Entails.eval a c178 := h 177 (by decide)
  have h26 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1454 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c275, some c273, some c48, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 57) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c1441, c275, c273, c48] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1455 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c1368, some c190, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 57) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c1254, c1368, c190] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1368 := derived1368 a h
  have h2 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c944, some c1451, some c1453, some c367, some c372, some c73, some c834, some c954, some c1454, some c188, some c24, some c1455, some c89, some c379, some c152, some c17, some c163, some c156, some c7, some c819, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 57) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c1441, c380, c944, c1451, c1453, c367, c372, c73, c834, c954, c1454, c188, c24, c1455, c89, c379, c152, c17, c163, c156, c7, c819] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c944 := derived944 a h
  have h3 : Entails.eval a c1451 := derived1451 a h
  have h4 : Entails.eval a c1453 := derived1453 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c834 := derived834 a h
  have h9 : Entails.eval a c954 := derived954 a h
  have h10 : Entails.eval a c1454 := derived1454 a h
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c1455 := derived1455 a h
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c379 := h 378 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c163 := h 162 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c7 := h 6 (by decide)
  have h21 : Entails.eval a c819 := derived819 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1457 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c944, some c1451, some c1453, some c1456, some c1241, some c67, some c834, some c374, some c379, some c569, some c152, some c17, some c163, some c7, some c169, some c819, some c1239, some c186, some c156, some c79, some c1363, some c281, some c1121, some c193, some c325, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 57) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c1441, c380, c944, c1451, c1453, c1456, c1241, c67, c834, c374, c379, c569, c152, c17, c163, c7, c169, c819, c1239, c186, c156, c79, c1363, c281, c1121, c193, c325] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c944 := derived944 a h
  have h3 : Entails.eval a c1451 := derived1451 a h
  have h4 : Entails.eval a c1453 := derived1453 a h
  have h5 : Entails.eval a c1456 := derived1456 a h
  have h6 : Entails.eval a c1241 := derived1241 a h
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c834 := derived834 a h
  have h9 : Entails.eval a c374 := h 373 (by decide)
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c569 := derived569 a h
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c7 := h 6 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c819 := derived819 a h
  have h18 : Entails.eval a c1239 := derived1239 a h
  have h19 : Entails.eval a c186 := h 185 (by decide)
  have h20 : Entails.eval a c156 := h 155 (by decide)
  have h21 : Entails.eval a c79 := h 78 (by decide)
  have h22 : Entails.eval a c1363 := derived1363 a h
  have h23 : Entails.eval a c281 := h 280 (by decide)
  have h24 : Entails.eval a c1121 := derived1121 a h
  have h25 : Entails.eval a c193 := h 192 (by decide)
  have h26 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1451, some c380, some c944, some c1453, some c1457, some c148, some c359, some c358, some c7, some c9, some c1164, some c379, some c162, some c163, some c90, some c1108, some c16, some c176, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 57) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c1441, c1451, c380, c944, c1453, c1457, c148, c359, c358, c7, c9, c1164, c379, c162, c163, c90, c1108, c16, c176] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1451 := derived1451 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c944 := derived944 a h
  have h4 : Entails.eval a c1453 := derived1453 a h
  have h5 : Entails.eval a c1457 := derived1457 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c1164 := derived1164 a h
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c1108 := derived1108 a h
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c66, some c964, some c1455, some c245, some c1452, some c67, some c78, some c569, some c275, some c947, some c54, some c59, some c330, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 57) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c1441, c66, c964, c1455, c245, c1452, c67, c78, c569, c275, c947, c54, c59, c330] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c964 := derived964 a h
  have h3 : Entails.eval a c1455 := derived1455 a h
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c1452 := derived1452 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c569 := derived569 a h
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c947 := derived947 a h
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1460 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c819, some c168, some c156, some c17, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 57) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c819, c168, c156, c17] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c819 := derived819 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1461 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1458, some c1451, some c380, some c944, some c1459, some c369, some c375, some c1449, some c73, some c24, some c834, some c1455, some c89, some c379, some c1460, some c7, some c9, some c163, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 57) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c1441, c1458, c1451, c380, c944, c1459, c369, c375, c1449, c73, c24, c834, c1455, c89, c379, c1460, c7, c9, c163] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1458 := derived1458 a h
  have h2 : Entails.eval a c1451 := derived1451 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c944 := derived944 a h
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c1449 := derived1449 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c834 := derived834 a h
  have h12 : Entails.eval a c1455 := derived1455 a h
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c379 := h 378 (by decide)
  have h15 : Entails.eval a c1460 := derived1460 a h
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c9, some c163, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 57) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c7, c9, c163] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1458, some c1451, some c380, some c944, some c1459, some c1461, some c1241, some c67, some c834, some c374, some c379, some c1462, some c168, some c1460, some c17, some c567, some c163, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 57) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c1441, c1458, c1451, c380, c944, c1459, c1461, c1241, c67, c834, c374, c379, c1462, c168, c1460, c17, c567, c163] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1458 := derived1458 a h
  have h2 : Entails.eval a c1451 := derived1451 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c944 := derived944 a h
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c1461 := derived1461 a h
  have h7 : Entails.eval a c1241 := derived1241 a h
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c834 := derived834 a h
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c1462 := derived1462 a h
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c1460 := derived1460 a h
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c567 := derived567 a h
  have h17 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1464 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c9, some c236, some c24, some c106, some c231, some c105, some c122, some c188, some c138, some c136, some c633, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 57) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c177, c9, c236, c24, c106, c231, c105, c122, c188, c138, c136, c633] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c327, some c325, some c215, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p1465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 57) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c327, c325, c215] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c327 := h 326 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c944, some c1459, some c1458, some c1463, some c148, some c359, some c7, some c9, some c371, some c1164, some c163, some c73, some c375, some c67, some c159, some c569, some c282, some c281, some c1464, some c113, some c233, some c231, some c1465, some c267, some c326, some c328, some c215, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 57) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c1441, c380, c944, c1459, c1458, c1463, c148, c359, c7, c9, c371, c1164, c163, c73, c375, c67, c159, c569, c282, c281, c1464, c113, c233, c231, c1465, c267, c326, c328, c215] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c944 := derived944 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c1458 := derived1458 a h
  have h5 : Entails.eval a c1463 := derived1463 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c1164 := derived1164 a h
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c67 := h 66 (by decide)
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c569 := derived569 a h
  have h18 : Entails.eval a c282 := h 281 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  have h20 : Entails.eval a c1464 := derived1464 a h
  have h21 : Entails.eval a c113 := h 112 (by decide)
  have h22 : Entails.eval a c233 := h 232 (by decide)
  have h23 : Entails.eval a c231 := h 230 (by decide)
  have h24 : Entails.eval a c1465 := derived1465 a h
  have h25 : Entails.eval a c267 := h 266 (by decide)
  have h26 : Entails.eval a c326 := h 325 (by decide)
  have h27 : Entails.eval a c328 := h 327 (by decide)
  have h28 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1467 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨12, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1282, some c359, some c1164, some c148, some c1393, some c358, some c162, some c379, some c90, some c16, some c172, some c182, some c163, some c176, some c1108, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 57) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c1441, c1282, c359, c1164, c148, c1393, c358, c162, c379, c90, c16, c172, c182, c163, c176, c1108] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c1164 := derived1164 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c1393 := derived1393 a h
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c182 := h 181 (by decide)
  have h13 : Entails.eval a c163 := h 162 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c1108 := derived1108 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c944, some c1459, some c1466, some c1282, some c148, some c359, some c7, some c1467, some c1394, some c371, some c67, some c78, some c74, some c569, some c282, some c42, some c326, some c54, some c59, some c330, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 57) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c1441, c380, c944, c1459, c1466, c1282, c148, c359, c7, c1467, c1394, c371, c67, c78, c74, c569, c282, c42, c326, c54, c59, c330] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c944 := derived944 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c1466 := derived1466 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c1467 := derived1467 a h
  have h10 : Entails.eval a c1394 := derived1394 a h
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c569 := derived569 a h
  have h16 : Entails.eval a c282 := h 281 (by decide)
  have h17 : Entails.eval a c42 := h 41 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c59 := h 58 (by decide)
  have h21 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1468, some c86, some c965, some c863, some c35, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 57) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c1468, c86, c965, c863, c35] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c1468 := derived1468 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c965 := derived965 a h
  have h3 : Entails.eval a c863 := derived863 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨47, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨45, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c275, some c281, some c198, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 57) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c275, c281, c198] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c275 := h 274 (by decide)
  have h1 : Entails.eval a c281 := h 280 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 57 := directClause ((⟨32, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨1, by decide⟩, true) :: (⟨2, by decide⟩, true) :: (⟨55, by decide⟩, true) :: (⟨4, by decide⟩, true) :: (⟨5, by decide⟩, false) :: (⟨7, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨6, by decide⟩, false) :: (⟨9, by decide⟩, true) :: (⟨10, by decide⟩, true) :: (⟨12, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨16, by decide⟩, false) :: (⟨14, by decide⟩, true) :: (⟨18, by decide⟩, true) :: (⟨17, by decide⟩, true) :: (⟨20, by decide⟩, false) :: (⟨21, by decide⟩, false) :: (⟨11, by decide⟩, false) :: (⟨23, by decide⟩, true) :: (⟨24, by decide⟩, true) :: (⟨22, by decide⟩, false) :: (⟨56, by decide⟩, true) :: (⟨27, by decide⟩, false) :: (⟨28, by decide⟩, true) :: (⟨29, by decide⟩, true) :: (⟨30, by decide⟩, true) :: (⟨31, by decide⟩, false) :: (⟨15, by decide⟩, false) :: (⟨33, by decide⟩, true) :: (⟨34, by decide⟩, false) :: (⟨25, by decide⟩, false) :: (⟨36, by decide⟩, false) :: (⟨37, by decide⟩, true) :: (⟨38, by decide⟩, false) :: (⟨39, by decide⟩, true) :: (⟨35, by decide⟩, true) :: (⟨41, by decide⟩, true) :: (⟨42, by decide⟩, false) :: (⟨43, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, false) :: (⟨46, by decide⟩, true) :: (⟨47, by decide⟩, false) :: (⟨40, by decide⟩, false) :: (⟨48, by decide⟩, true) :: (⟨50, by decide⟩, true) :: (⟨49, by decide⟩, false) :: (⟨52, by decide⟩, false) :: (⟨53, by decide⟩, true) :: (⟨51, by decide⟩, true) :: (⟨54, by decide⟩, false) :: []) (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c399, some c212, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 57) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c1441, c399, c212] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c399 := h 398 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨56, by decide⟩, true), (⟨37, by decide⟩, true), (⟨47, by decide⟩, false), (⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1469, some c380, some c87, some c1459, some c169, some c1104, some c834, some c16, some c162, some c180, some c14, some c236, some c105, some c224, some c1470, some c107, some c32, some c372, some c1468, some c1367, some c927, some c367, some c156, some c960, some c36, some c198, some c594, some c317, some c127, some c35, some c207, some c37, some c58, some c288, some c919, some c143, some c266, some c1471, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 57) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c1441, c1469, c380, c87, c1459, c169, c1104, c834, c16, c162, c180, c14, c236, c105, c224, c1470, c107, c32, c372, c1468, c1367, c927, c367, c156, c960, c36, c198, c594, c317, c127, c35, c207, c37, c58, c288, c919, c143, c266, c1471] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c1459 := derived1459 a h
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c1104 := derived1104 a h
  have h7 : Entails.eval a c834 := derived834 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c180 := h 179 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c236 := h 235 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c1470 := derived1470 a h
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c1468 := derived1468 a h
  have h20 : Entails.eval a c1367 := derived1367 a h
  have h21 : Entails.eval a c927 := derived927 a h
  have h22 : Entails.eval a c367 := h 366 (by decide)
  have h23 : Entails.eval a c156 := h 155 (by decide)
  have h24 : Entails.eval a c960 := derived960 a h
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c198 := h 197 (by decide)
  have h27 : Entails.eval a c594 := derived594 a h
  have h28 : Entails.eval a c317 := h 316 (by decide)
  have h29 : Entails.eval a c127 := h 126 (by decide)
  have h30 : Entails.eval a c35 := h 34 (by decide)
  have h31 : Entails.eval a c207 := h 206 (by decide)
  have h32 : Entails.eval a c37 := h 36 (by decide)
  have h33 : Entails.eval a c58 := h 57 (by decide)
  have h34 : Entails.eval a c288 := h 287 (by decide)
  have h35 : Entails.eval a c919 := derived919 a h
  have h36 : Entails.eval a c143 := h 142 (by decide)
  have h37 : Entails.eval a c266 := h 265 (by decide)
  have h38 : Entails.eval a c1471 := derived1471 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1473 : DefaultClause 57 := directClause ((⟨19, by decide⟩, false) :: (⟨56, by decide⟩, true) :: (⟨1, by decide⟩, true) :: (⟨2, by decide⟩, true) :: (⟨4, by decide⟩, true) :: (⟨7, by decide⟩, false) :: (⟨5, by decide⟩, false) :: (⟨6, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨11, by decide⟩, false) :: (⟨9, by decide⟩, true) :: (⟨10, by decide⟩, true) :: (⟨12, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨16, by decide⟩, false) :: (⟨14, by decide⟩, true) :: (⟨18, by decide⟩, true) :: (⟨17, by decide⟩, true) :: (⟨20, by decide⟩, false) :: (⟨21, by decide⟩, false) :: (⟨22, by decide⟩, false) :: (⟨23, by decide⟩, true) :: (⟨24, by decide⟩, true) :: (⟨25, by decide⟩, true) :: (⟨26, by decide⟩, false) :: (⟨27, by decide⟩, true) :: (⟨28, by decide⟩, false) :: (⟨29, by decide⟩, true) :: (⟨40, by decide⟩, true) :: (⟨15, by decide⟩, false) :: (⟨32, by decide⟩, false) :: (⟨33, by decide⟩, false) :: (⟨31, by decide⟩, true) :: (⟨35, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨37, by decide⟩, true) :: (⟨36, by decide⟩, true) :: (⟨38, by decide⟩, true) :: (⟨39, by decide⟩, false) :: (⟨41, by decide⟩, true) :: (⟨42, by decide⟩, false) :: (⟨43, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, false) :: (⟨46, by decide⟩, true) :: (⟨47, by decide⟩, false) :: (⟨48, by decide⟩, true) :: (⟨49, by decide⟩, false) :: (⟨50, by decide⟩, true) :: (⟨51, by decide⟩, true) :: (⟨52, by decide⟩, false) :: (⟨53, by decide⟩, true) :: (⟨54, by decide⟩, false) :: (⟨55, by decide⟩, true) :: []) (by decide +kernel) (by decide +kernel)
def f1473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c400, some c266, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1473 : lratChecker f1473 p1473 = .success := by decide +kernel
theorem unsat1473 : Unsatisfiable (PosFin 57) f1473 := by
  apply lratCheckerSound f1473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1473
  · intro a ha; simp [p1473] at ha; subst a; trivial
  · exact checked1473
theorem derived1473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1473 := by
  apply localUnsat_implies_entails f1473 [c1441, c400, c266] c1473 unsat1473 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c400 := h 399 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1474 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨37, by decide⟩, true), (⟨47, by decide⟩, false), (⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1469, some c380, some c87, some c1459, some c169, some c1104, some c834, some c16, some c162, some c180, some c14, some c236, some c105, some c224, some c1470, some c107, some c32, some c372, some c1468, some c1367, some c927, some c367, some c156, some c960, some c1472, some c273, some c37, some c47, some c317, some c141, some c287, some c127, some c209, some c194, some c207, some c201, some c143, some c350, some c1473, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]]
theorem checked1474 : lratChecker f1474 p1474 = .success := by decide +kernel
theorem unsat1474 : Unsatisfiable (PosFin 57) f1474 := by
  apply lratCheckerSound f1474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1474
  · intro a ha; simp [p1474] at ha; subst a; trivial
  · exact checked1474
theorem derived1474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1474 := by
  apply localUnsat_implies_entails f1474 [c1441, c1469, c380, c87, c1459, c169, c1104, c834, c16, c162, c180, c14, c236, c105, c224, c1470, c107, c32, c372, c1468, c1367, c927, c367, c156, c960, c1472, c273, c37, c47, c317, c141, c287, c127, c209, c194, c207, c201, c143, c350, c1473] c1474 unsat1474 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c1459 := derived1459 a h
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c1104 := derived1104 a h
  have h7 : Entails.eval a c834 := derived834 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c180 := h 179 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c236 := h 235 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c1470 := derived1470 a h
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c1468 := derived1468 a h
  have h20 : Entails.eval a c1367 := derived1367 a h
  have h21 : Entails.eval a c927 := derived927 a h
  have h22 : Entails.eval a c367 := h 366 (by decide)
  have h23 : Entails.eval a c156 := h 155 (by decide)
  have h24 : Entails.eval a c960 := derived960 a h
  have h25 : Entails.eval a c1472 := derived1472 a h
  have h26 : Entails.eval a c273 := h 272 (by decide)
  have h27 : Entails.eval a c37 := h 36 (by decide)
  have h28 : Entails.eval a c47 := h 46 (by decide)
  have h29 : Entails.eval a c317 := h 316 (by decide)
  have h30 : Entails.eval a c141 := h 140 (by decide)
  have h31 : Entails.eval a c287 := h 286 (by decide)
  have h32 : Entails.eval a c127 := h 126 (by decide)
  have h33 : Entails.eval a c209 := h 208 (by decide)
  have h34 : Entails.eval a c194 := h 193 (by decide)
  have h35 : Entails.eval a c207 := h 206 (by decide)
  have h36 : Entails.eval a c201 := h 200 (by decide)
  have h37 : Entails.eval a c143 := h 142 (by decide)
  have h38 : Entails.eval a c350 := h 349 (by decide)
  have h39 : Entails.eval a c1473 := derived1473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1475 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c950, some c943, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1475 : lratChecker f1475 p1475 = .success := by decide +kernel
theorem unsat1475 : Unsatisfiable (PosFin 57) f1475 := by
  apply lratCheckerSound f1475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1475
  · intro a ha; simp [p1475] at ha; subst a; trivial
  · exact checked1475
theorem derived1475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1475 := by
  apply localUnsat_implies_entails f1475 [c1441, c950, c943] c1475 unsat1475 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c943 := derived943 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1476 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c169, some c834, some c1469, some c87, some c16, some c162, some c180, some c1459, some c14, some c236, some c105, some c224, some c1468, some c372, some c367, some c960, some c1475, some c1104, some c1474, some c319, some c325, some c209, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1476 : lratChecker f1476 p1476 = .success := by decide +kernel
theorem unsat1476 : Unsatisfiable (PosFin 57) f1476 := by
  apply lratCheckerSound f1476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1476
  · intro a ha; simp [p1476] at ha; subst a; trivial
  · exact checked1476
theorem derived1476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1476 := by
  apply localUnsat_implies_entails f1476 [c1441, c380, c169, c834, c1469, c87, c16, c162, c180, c1459, c14, c236, c105, c224, c1468, c372, c367, c960, c1475, c1104, c1474, c319, c325, c209] c1476 unsat1476 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c834 := derived834 a h
  have h4 : Entails.eval a c1469 := derived1469 a h
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c1459 := derived1459 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c236 := h 235 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c1468 := derived1468 a h
  have h15 : Entails.eval a c372 := h 371 (by decide)
  have h16 : Entails.eval a c367 := h 366 (by decide)
  have h17 : Entails.eval a c960 := derived960 a h
  have h18 : Entails.eval a c1475 := derived1475 a h
  have h19 : Entails.eval a c1104 := derived1104 a h
  have h20 : Entails.eval a c1474 := derived1474 a h
  have h21 : Entails.eval a c319 := h 318 (by decide)
  have h22 : Entails.eval a c325 := h 324 (by decide)
  have h23 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1477 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨37, by decide⟩, true), (⟨47, by decide⟩, false), (⟨23, by decide⟩, true), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c275, some c1470, some c36, some c224, some c222, some c317, some c211, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1477 : lratChecker f1477 p1477 = .success := by decide +kernel
theorem unsat1477 : Unsatisfiable (PosFin 57) f1477 := by
  apply lratCheckerSound f1477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1477
  · intro a ha; simp [p1477] at ha; subst a; trivial
  · exact checked1477
theorem derived1477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1477 := by
  apply localUnsat_implies_entails f1477 [c275, c1470, c36, c224, c222, c317, c211] c1477 unsat1477 (by rfl) a
  have h0 : Entails.eval a c275 := h 274 (by decide)
  have h1 : Entails.eval a c1470 := derived1470 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c222 := h 221 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1478 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1469, some c367, some c1468, some c380, some c834, some c960, some c87, some c169, some c16, some c1459, some c1104, some c372, some c1475, some c366, some c1477, some c191, some c224, some c107, some c237, some c32, some c1476, some c162, some c180, some c156, some c14, some c36, some c209, some c273, some c143, some c37, some c47, some c214, some c287, some c127, some c141, some c354, some c35, some c196, some c201, some c171, some c266, some c401, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]]
theorem checked1478 : lratChecker f1478 p1478 = .success := by decide +kernel
theorem unsat1478 : Unsatisfiable (PosFin 57) f1478 := by
  apply lratCheckerSound f1478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1478
  · intro a ha; simp [p1478] at ha; subst a; trivial
  · exact checked1478
theorem derived1478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1478 := by
  apply localUnsat_implies_entails f1478 [c1441, c1469, c367, c1468, c380, c834, c960, c87, c169, c16, c1459, c1104, c372, c1475, c366, c1477, c191, c224, c107, c237, c32, c1476, c162, c180, c156, c14, c36, c209, c273, c143, c37, c47, c214, c287, c127, c141, c354, c35, c196, c201, c171, c266, c401] c1478 unsat1478 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c1468 := derived1468 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c834 := derived834 a h
  have h6 : Entails.eval a c960 := derived960 a h
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c1459 := derived1459 a h
  have h11 : Entails.eval a c1104 := derived1104 a h
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c1475 := derived1475 a h
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c1477 := derived1477 a h
  have h16 : Entails.eval a c191 := h 190 (by decide)
  have h17 : Entails.eval a c224 := h 223 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c32 := h 31 (by decide)
  have h21 : Entails.eval a c1476 := derived1476 a h
  have h22 : Entails.eval a c162 := h 161 (by decide)
  have h23 : Entails.eval a c180 := h 179 (by decide)
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c14 := h 13 (by decide)
  have h26 : Entails.eval a c36 := h 35 (by decide)
  have h27 : Entails.eval a c209 := h 208 (by decide)
  have h28 : Entails.eval a c273 := h 272 (by decide)
  have h29 : Entails.eval a c143 := h 142 (by decide)
  have h30 : Entails.eval a c37 := h 36 (by decide)
  have h31 : Entails.eval a c47 := h 46 (by decide)
  have h32 : Entails.eval a c214 := h 213 (by decide)
  have h33 : Entails.eval a c287 := h 286 (by decide)
  have h34 : Entails.eval a c127 := h 126 (by decide)
  have h35 : Entails.eval a c141 := h 140 (by decide)
  have h36 : Entails.eval a c354 := h 353 (by decide)
  have h37 : Entails.eval a c35 := h 34 (by decide)
  have h38 : Entails.eval a c196 := h 195 (by decide)
  have h39 : Entails.eval a c201 := h 200 (by decide)
  have h40 : Entails.eval a c171 := h 170 (by decide)
  have h41 : Entails.eval a c266 := h 265 (by decide)
  have h42 : Entails.eval a c401 := h 400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1479 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c372, some c1468, some c1469, some c367, some c834, some c960, some c1475, some c366, some c1476, some c169, some c87, some c16, some c162, some c180, some c156, some c1459, some c14, some c1104, some c1477, some c191, some c224, some c32, some c107, some c237, some c1478, some c594, some c317, some c35, some c207, some c37, some c58, some c287, some c288, some c273, some c143, some c203, some c266, some c198, some c212, some c125, some c919, some c402, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]]
theorem checked1479 : lratChecker f1479 p1479 = .success := by decide +kernel
theorem unsat1479 : Unsatisfiable (PosFin 57) f1479 := by
  apply lratCheckerSound f1479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1479
  · intro a ha; simp [p1479] at ha; subst a; trivial
  · exact checked1479
theorem derived1479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1479 := by
  apply localUnsat_implies_entails f1479 [c1441, c380, c372, c1468, c1469, c367, c834, c960, c1475, c366, c1476, c169, c87, c16, c162, c180, c156, c1459, c14, c1104, c1477, c191, c224, c32, c107, c237, c1478, c594, c317, c35, c207, c37, c58, c287, c288, c273, c143, c203, c266, c198, c212, c125, c919, c402] c1479 unsat1479 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1468 := derived1468 a h
  have h4 : Entails.eval a c1469 := derived1469 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c834 := derived834 a h
  have h7 : Entails.eval a c960 := derived960 a h
  have h8 : Entails.eval a c1475 := derived1475 a h
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c1476 := derived1476 a h
  have h11 : Entails.eval a c169 := h 168 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c162 := h 161 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c1459 := derived1459 a h
  have h18 : Entails.eval a c14 := h 13 (by decide)
  have h19 : Entails.eval a c1104 := derived1104 a h
  have h20 : Entails.eval a c1477 := derived1477 a h
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c224 := h 223 (by decide)
  have h23 : Entails.eval a c32 := h 31 (by decide)
  have h24 : Entails.eval a c107 := h 106 (by decide)
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c1478 := derived1478 a h
  have h27 : Entails.eval a c594 := derived594 a h
  have h28 : Entails.eval a c317 := h 316 (by decide)
  have h29 : Entails.eval a c35 := h 34 (by decide)
  have h30 : Entails.eval a c207 := h 206 (by decide)
  have h31 : Entails.eval a c37 := h 36 (by decide)
  have h32 : Entails.eval a c58 := h 57 (by decide)
  have h33 : Entails.eval a c287 := h 286 (by decide)
  have h34 : Entails.eval a c288 := h 287 (by decide)
  have h35 : Entails.eval a c273 := h 272 (by decide)
  have h36 : Entails.eval a c143 := h 142 (by decide)
  have h37 : Entails.eval a c203 := h 202 (by decide)
  have h38 : Entails.eval a c266 := h 265 (by decide)
  have h39 : Entails.eval a c198 := h 197 (by decide)
  have h40 : Entails.eval a c212 := h 211 (by decide)
  have h41 : Entails.eval a c125 := h 124 (by decide)
  have h42 : Entails.eval a c919 := derived919 a h
  have h43 : Entails.eval a c402 := h 401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1480 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c834, some c372, some c367, some c1469, some c1459, some c87, some c1468, some c960, some c169, some c1104, some c1475, some c366, some c1479, some c319, some c325, some c947, some c209, some c275, some c273, some c224, some c222, some c200, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1480 : lratChecker f1480 p1480 = .success := by decide +kernel
theorem unsat1480 : Unsatisfiable (PosFin 57) f1480 := by
  apply lratCheckerSound f1480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1480
  · intro a ha; simp [p1480] at ha; subst a; trivial
  · exact checked1480
theorem derived1480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1480 := by
  apply localUnsat_implies_entails f1480 [c1441, c380, c834, c372, c367, c1469, c1459, c87, c1468, c960, c169, c1104, c1475, c366, c1479, c319, c325, c947, c209, c275, c273, c224, c222, c200] c1480 unsat1480 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c834 := derived834 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c1469 := derived1469 a h
  have h6 : Entails.eval a c1459 := derived1459 a h
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c1468 := derived1468 a h
  have h9 : Entails.eval a c960 := derived960 a h
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c1104 := derived1104 a h
  have h12 : Entails.eval a c1475 := derived1475 a h
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c1479 := derived1479 a h
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  have h17 : Entails.eval a c947 := derived947 a h
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c275 := h 274 (by decide)
  have h20 : Entails.eval a c273 := h 272 (by decide)
  have h21 : Entails.eval a c224 := h 223 (by decide)
  have h22 : Entails.eval a c222 := h 221 (by decide)
  have h23 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1481 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c273, some c121, some c47, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1481 : lratChecker f1481 p1481 = .success := by decide +kernel
theorem unsat1481 : Unsatisfiable (PosFin 57) f1481 := by
  apply lratCheckerSound f1481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1481
  · intro a ha; simp [p1481] at ha; subst a; trivial
  · exact checked1481
theorem derived1481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1481 := by
  apply localUnsat_implies_entails f1481 [c1441, c273, c121, c47] c1481 unsat1481 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1482 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1481, some c36, some c137, some c317, some c58, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1482 : lratChecker f1482 p1482 = .success := by decide +kernel
theorem unsat1482 : Unsatisfiable (PosFin 57) f1482 := by
  apply lratCheckerSound f1482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1482
  · intro a ha; simp [p1482] at ha; subst a; trivial
  · exact checked1482
theorem derived1482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1482 := by
  apply localUnsat_implies_entails f1482 [c1441, c1481, c36, c137, c317, c58] c1482 unsat1482 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1483 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c1469, some c1468, some c380, some c834, some c1480, some c1482, some c162, some c163, some c17, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1483 : lratChecker f1483 p1483 = .success := by decide +kernel
theorem unsat1483 : Unsatisfiable (PosFin 57) f1483 := by
  apply lratCheckerSound f1483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1483
  · intro a ha; simp [p1483] at ha; subst a; trivial
  · exact checked1483
theorem derived1483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1483 := by
  apply localUnsat_implies_entails f1483 [c372, c1469, c1468, c380, c834, c1480, c1482, c162, c163, c17] c1483 unsat1483 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c1468 := derived1468 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c834 := derived834 a h
  have h5 : Entails.eval a c1480 := derived1480 a h
  have h6 : Entails.eval a c1482 := derived1482 a h
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1484 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c16, some c164, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1484 : lratChecker f1484 p1484 = .success := by decide +kernel
theorem unsat1484 : Unsatisfiable (PosFin 57) f1484 := by
  apply lratCheckerSound f1484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1484
  · intro a ha; simp [p1484] at ha; subst a; trivial
  · exact checked1484
theorem derived1484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1484 := by
  apply localUnsat_implies_entails f1484 [c14, c16, c164] c1484 unsat1484 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1485 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c367, some c1469, some c1459, some c380, some c87, some c1483, some c837, some c1484, some c172, some c169, some c177, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1485 : lratChecker f1485 p1485 = .success := by decide +kernel
theorem unsat1485 : Unsatisfiable (PosFin 57) f1485 := by
  apply lratCheckerSound f1485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1485
  · intro a ha; simp [p1485] at ha; subst a; trivial
  · exact checked1485
theorem derived1485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1485 := by
  apply localUnsat_implies_entails f1485 [c372, c367, c1469, c1459, c380, c87, c1483, c837, c1484, c172, c169, c177] c1485 unsat1485 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c1469 := derived1469 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c1483 := derived1483 a h
  have h7 : Entails.eval a c837 := derived837 a h
  have h8 : Entails.eval a c1484 := derived1484 a h
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1486 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c38, some c47, some c318, some c273, some c36, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1486 : lratChecker f1486 p1486 = .success := by decide +kernel
theorem unsat1486 : Unsatisfiable (PosFin 57) f1486 := by
  apply lratCheckerSound f1486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1486
  · intro a ha; simp [p1486] at ha; subst a; trivial
  · exact checked1486
theorem derived1486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1486 := by
  apply localUnsat_implies_entails f1486 [c1441, c38, c47, c318, c273, c36] c1486 unsat1486 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1487 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1469, some c1468, some c380, some c367, some c372, some c1485, some c379, some c152, some c1460, some c17, some c1482, some c163, some c1486, some c274, some c287, some c36, some c35, some c594, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1487 : lratChecker f1487 p1487 = .success := by decide +kernel
theorem unsat1487 : Unsatisfiable (PosFin 57) f1487 := by
  apply lratCheckerSound f1487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1487
  · intro a ha; simp [p1487] at ha; subst a; trivial
  · exact checked1487
theorem derived1487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1487 := by
  apply localUnsat_implies_entails f1487 [c1441, c1469, c1468, c380, c367, c372, c1485, c379, c152, c1460, c17, c1482, c163, c1486, c274, c287, c36, c35, c594] c1487 unsat1487 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c1468 := derived1468 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c1485 := derived1485 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c1460 := derived1460 a h
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c1482 := derived1482 a h
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c1486 := derived1486 a h
  have h14 : Entails.eval a c274 := h 273 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c594 := derived594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1488 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c594, some c318, some c35, some c38, some c287, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1488 : lratChecker f1488 p1488 = .success := by decide +kernel
theorem unsat1488 : Unsatisfiable (PosFin 57) f1488 := by
  apply lratCheckerSound f1488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1488
  · intro a ha; simp [p1488] at ha; subst a; trivial
  · exact checked1488
theorem derived1488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1488 := by
  apply localUnsat_implies_entails f1488 [c1441, c594, c318, c35, c38, c287] c1488 unsat1488 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1489 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1469, some c1459, some c380, some c87, some c1468, some c1487, some c67, some c77, some c379, some c368, some c834, some c152, some c1239, some c365, some c17, some c1276, some c169, some c699, some c1488, some c36, some c274, some c122, some c38, some c191, some c340, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1489 : lratChecker f1489 p1489 = .success := by decide +kernel
theorem unsat1489 : Unsatisfiable (PosFin 57) f1489 := by
  apply lratCheckerSound f1489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1489
  · intro a ha; simp [p1489] at ha; subst a; trivial
  · exact checked1489
theorem derived1489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1489 := by
  apply localUnsat_implies_entails f1489 [c1441, c1469, c1459, c380, c87, c1468, c1487, c67, c77, c379, c368, c834, c152, c1239, c365, c17, c1276, c169, c699, c1488, c36, c274, c122, c38, c191, c340] c1489 unsat1489 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c1468 := derived1468 a h
  have h6 : Entails.eval a c1487 := derived1487 a h
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c834 := derived834 a h
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c1239 := derived1239 a h
  have h14 : Entails.eval a c365 := h 364 (by decide)
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c1276 := derived1276 a h
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c699 := derived699 a h
  have h19 : Entails.eval a c1488 := derived1488 a h
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c274 := h 273 (by decide)
  have h22 : Entails.eval a c122 := h 121 (by decide)
  have h23 : Entails.eval a c38 := h 37 (by decide)
  have h24 : Entails.eval a c191 := h 190 (by decide)
  have h25 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1490 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨26, by decide⟩, false), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c273, some c37, some c321, some c275, some c191, some c266, some c224, some c283, some c107, some c201, some c226, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1490 : lratChecker f1490 p1490 = .success := by decide +kernel
theorem unsat1490 : Unsatisfiable (PosFin 57) f1490 := by
  apply lratCheckerSound f1490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1490
  · intro a ha; simp [p1490] at ha; subst a; trivial
  · exact checked1490
theorem derived1490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1490 := by
  apply localUnsat_implies_entails f1490 [c1441, c273, c37, c321, c275, c191, c266, c224, c283, c107, c201, c226] c1490 unsat1490 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1491 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c275, some c273, some c1490, some c325, some c209, some c224, some c222, some c200, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1491 : lratChecker f1491 p1491 = .success := by decide +kernel
theorem unsat1491 : Unsatisfiable (PosFin 57) f1491 := by
  apply lratCheckerSound f1491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1491
  · intro a ha; simp [p1491] at ha; subst a; trivial
  · exact checked1491
theorem derived1491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1491 := by
  apply localUnsat_implies_entails f1491 [c36, c275, c273, c1490, c325, c209, c224, c222, c200] c1491 unsat1491 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c1490 := derived1490 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c224 := h 223 (by decide)
  have h7 : Entails.eval a c222 := h 221 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1492 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1491, some c319, some c594, some c317, some c1477, some c1490, some c35, some c191, some c288, some c224, some c197, some c266, some c226, some c327, some c212, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1492 : lratChecker f1492 p1492 = .success := by decide +kernel
theorem unsat1492 : Unsatisfiable (PosFin 57) f1492 := by
  apply lratCheckerSound f1492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1492
  · intro a ha; simp [p1492] at ha; subst a; trivial
  · exact checked1492
theorem derived1492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1492 := by
  apply localUnsat_implies_entails f1492 [c1441, c1491, c319, c594, c317, c1477, c1490, c35, c191, c288, c224, c197, c266, c226, c327, c212] c1492 unsat1492 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1491 := derived1491 a h
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c1477 := derived1477 a h
  have h6 : Entails.eval a c1490 := derived1490 a h
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c226 := h 225 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1493 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c37, some c47, some c132, some c287, some c35, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 57) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c1441, c37, c47, c132, c287, c35] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1494 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c375, some c369, some c1469, some c1459, some c380, some c87, some c1468, some c169, some c1460, some c1104, some c14, some c16, some c1475, some c154, some c366, some c1492, some c837, some c151, some c180, some c1365, some c1366, some c34, some c237, some c1493, some c116, some c125, some c196, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 57) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c1489, c375, c369, c1469, c1459, c380, c87, c1468, c169, c1460, c1104, c14, c16, c1475, c154, c366, c1492, c837, c151, c180, c1365, c1366, c34, c237, c1493, c116, c125, c196] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c1469 := derived1469 a h
  have h4 : Entails.eval a c1459 := derived1459 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c1468 := derived1468 a h
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c1460 := derived1460 a h
  have h10 : Entails.eval a c1104 := derived1104 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c1475 := derived1475 a h
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c366 := h 365 (by decide)
  have h16 : Entails.eval a c1492 := derived1492 a h
  have h17 : Entails.eval a c837 := derived837 a h
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c180 := h 179 (by decide)
  have h20 : Entails.eval a c1365 := derived1365 a h
  have h21 : Entails.eval a c1366 := derived1366 a h
  have h22 : Entails.eval a c34 := h 33 (by decide)
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c1493 := derived1493 a h
  have h25 : Entails.eval a c116 := h 115 (by decide)
  have h26 : Entails.eval a c125 := h 124 (by decide)
  have h27 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c380, some c163, some c815, some c17, some c182, some c1366, some c927, some c825, some c379, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 57) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c375, c380, c163, c815, c17, c182, c1366, c927, c825, c379] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c163 := h 162 (by decide)
  have h3 : Entails.eval a c815 := derived815 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c1366 := derived1366 a h
  have h7 : Entails.eval a c927 := derived927 a h
  have h8 : Entails.eval a c825 := derived825 a h
  have h9 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1496 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1469, some c1459, some c1468, some c1494, some c1482, some c1495, some c1486, some c1488, some c274, some c36, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 57) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c1489, c1469, c1459, c1468, c1494, c1482, c1495, c1486, c1488, c274, c36] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1469 := derived1469 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c1468 := derived1468 a h
  have h4 : Entails.eval a c1494 := derived1494 a h
  have h5 : Entails.eval a c1482 := derived1482 a h
  have h6 : Entails.eval a c1495 := derived1495 a h
  have h7 : Entails.eval a c1486 := derived1486 a h
  have h8 : Entails.eval a c1488 := derived1488 a h
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1468, some c1496, some c67, some c77, some c1488, some c36, some c274, some c38, some c47, some c331, some c286, some c35, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 57) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c1441, c1468, c1496, c67, c77, c1488, c36, c274, c38, c47, c331, c286, c35] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1468 := derived1468 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c1488 := derived1488 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1468, some c380, some c1497, some c102, some c1273, some c834, some c374, some c962, some c1254, some c1368, some c38, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 57) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1468, c380, c1497, c102, c1273, c834, c374, c962, c1254, c1368, c38] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1468 := derived1468 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c1497 := derived1497 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c1273 := derived1273 a h
  have h5 : Entails.eval a c834 := derived834 a h
  have h6 : Entails.eval a c374 := h 373 (by decide)
  have h7 : Entails.eval a c962 := derived962 a h
  have h8 : Entails.eval a c1254 := derived1254 a h
  have h9 : Entails.eval a c1368 := derived1368 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c1368, some c38, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 57) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c1254, c1368, c38] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1368 := derived1368 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1468, some c380, some c1498, some c66, some c359, some c102, some c1164, some c77, some c1499, some c89, some c962, some c379, some c375, some c358, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 57) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c1441, c1468, c380, c1498, c66, c359, c102, c1164, c77, c1499, c89, c962, c379, c375, c358] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1468 := derived1468 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c1498 := derived1498 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c1164 := derived1164 a h
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c1499 := derived1499 a h
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c962 := derived962 a h
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c375 := h 374 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c278, some c322, some c37, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 57) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c1441, c278, c322, c37] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c322 := h 321 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c148, some c66, some c1394, some c358, some c379, some c1501, some c72, some c81, some c1089, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 57) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c1282, c148, c66, c1394, c358, c379, c1501, c72, c81, c1089] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c1501 := derived1501 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c1089 := derived1089 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1503 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c1468, some c1500, some c1282, some c1135, some c1097, some c66, some c148, some c359, some c1502, some c77, some c1185, some c834, some c1164, some c8, some c160, some c155, some c177, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 57) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1441, c380, c1468, c1500, c1282, c1135, c1097, c66, c148, c359, c1502, c77, c1185, c834, c1164, c8, c160, c155, c177] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c1468 := derived1468 a h
  have h3 : Entails.eval a c1500 := derived1500 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1135 := derived1135 a h
  have h6 : Entails.eval a c1097 := derived1097 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c1502 := derived1502 a h
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c1185 := derived1185 a h
  have h13 : Entails.eval a c834 := derived834 a h
  have h14 : Entails.eval a c1164 := derived1164 a h
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c155 := h 154 (by decide)
  have h18 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c882, some c1307, some c154, some c1282, some c835, some c87, some c379, some c99, some c903, some c860, some c80, some c834, some c82, some c837, some c15, some c5, some c164, some c172, some c568, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 57) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1441, c882, c1307, c154, c1282, c835, c87, c379, c99, c903, c860, c80, c834, c82, c837, c15, c5, c164, c172, c568] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c835 := derived835 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c903 := derived903 a h
  have h10 : Entails.eval a c860 := derived860 a h
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c834 := derived834 a h
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c837 := derived837 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c568 := derived568 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨2, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1307, some c80, some c956, some c845, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 57) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c1307, c80, c956, c845] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c1307 := derived1307 a h
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c956 := derived956 a h
  have h3 : Entails.eval a c845 := derived845 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c958, some c845, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 57) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c882, c958, c845] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c958 := derived958 a h
  have h2 : Entails.eval a c845 := derived845 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c102, some c1505, some c82, some c834, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 57) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1282, c102, c1505, c82, c834] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c834 := derived834 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c1503, some c1323, some c1504, some c1282, some c1307, some c1506, some c1507, some c882, some c154, some c9, some c102, some c834, some c954, some c1454, some c962, some c859, some c188, some c830, some c379, some c26, some c18, some c224, some c222, some c321, some c330, some c168, some c1277, some c110, some c63, some c207, some c145, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 57) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c1441, c380, c1503, c1323, c1504, c1282, c1307, c1506, c1507, c882, c154, c9, c102, c834, c954, c1454, c962, c859, c188, c830, c379, c26, c18, c224, c222, c321, c330, c168, c1277, c110, c63, c207, c145] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c1503 := derived1503 a h
  have h3 : Entails.eval a c1323 := derived1323 a h
  have h4 : Entails.eval a c1504 := derived1504 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1307 := derived1307 a h
  have h7 : Entails.eval a c1506 := derived1506 a h
  have h8 : Entails.eval a c1507 := derived1507 a h
  have h9 : Entails.eval a c882 := derived882 a h
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c834 := derived834 a h
  have h14 : Entails.eval a c954 := derived954 a h
  have h15 : Entails.eval a c1454 := derived1454 a h
  have h16 : Entails.eval a c962 := derived962 a h
  have h17 : Entails.eval a c859 := derived859 a h
  have h18 : Entails.eval a c188 := h 187 (by decide)
  have h19 : Entails.eval a c830 := derived830 a h
  have h20 : Entails.eval a c379 := h 378 (by decide)
  have h21 : Entails.eval a c26 := h 25 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c224 := h 223 (by decide)
  have h24 : Entails.eval a c222 := h 221 (by decide)
  have h25 : Entails.eval a c321 := h 320 (by decide)
  have h26 : Entails.eval a c330 := h 329 (by decide)
  have h27 : Entails.eval a c168 := h 167 (by decide)
  have h28 : Entails.eval a c1277 := derived1277 a h
  have h29 : Entails.eval a c110 := h 109 (by decide)
  have h30 : Entails.eval a c63 := h 62 (by decide)
  have h31 : Entails.eval a c207 := h 206 (by decide)
  have h32 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1509 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1282, some c380, some c1503, some c1323, some c1504, some c102, some c1307, some c1506, some c1507, some c1508, some c69, some c830, some c321, some c61, some c63, some c340, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 57) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1441, c1282, c380, c1503, c1323, c1504, c102, c1307, c1506, c1507, c1508, c69, c830, c321, c61, c63, c340] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c1503 := derived1503 a h
  have h4 : Entails.eval a c1323 := derived1323 a h
  have h5 : Entails.eval a c1504 := derived1504 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c1307 := derived1307 a h
  have h8 : Entails.eval a c1506 := derived1506 a h
  have h9 : Entails.eval a c1507 := derived1507 a h
  have h10 : Entails.eval a c1508 := derived1508 a h
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c830 := derived830 a h
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1503, some c1323, some c380, some c1282, some c1504, some c1509, some c1241, some c1240, some c834, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 57) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c1503, c1323, c380, c1282, c1504, c1509, c1241, c1240, c834] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c1503 := derived1503 a h
  have h1 : Entails.eval a c1323 := derived1323 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1504 := derived1504 a h
  have h5 : Entails.eval a c1509 := derived1509 a h
  have h6 : Entails.eval a c1241 := derived1241 a h
  have h7 : Entails.eval a c1240 := derived1240 a h
  have h8 : Entails.eval a c834 := derived834 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨5, by decide⟩, true), (⟨42, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c358, some c379, some c845, some c859, some c82, some c834, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 57) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c66, c358, c379, c845, c859, c82, c834] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c859 := derived859 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c834 := derived834 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨42, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c148, some c66, some c882, some c102, some c9, some c154, some c1511, some c375, some c1241, some c1240, some c834, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 57) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c148, c66, c882, c102, c9, c154, c1511, c375, c1241, c1240, c834] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c148 := h 147 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c882 := derived882 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c1511 := derived1511 a h
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c1241 := derived1241 a h
  have h9 : Entails.eval a c1240 := derived1240 a h
  have h10 : Entails.eval a c834 := derived834 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨42, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c1512, some c94, some c99, some c66, some c148, some c1, some c1511, some c80, some c1278, some c1185, some c834, some c155, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 57) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c882, c1512, c94, c99, c66, c148, c1, c1511, c80, c1278, c1185, c834, c155] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c1512 := derived1512 a h
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c1511 := derived1511 a h
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c1278 := derived1278 a h
  have h10 : Entails.eval a c1185 := derived1185 a h
  have h11 : Entails.eval a c834 := derived834 a h
  have h12 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1514 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c380, some c1503, some c882, some c1323, some c1510, some c66, some c148, some c359, some c1, some c1512, some c72, some c1513, some c371, some c375, some c1240, some c834, some c78, some c155, some c1278, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 57) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c1441, c380, c1503, c882, c1323, c1510, c66, c148, c359, c1, c1512, c72, c1513, c371, c375, c1240, c834, c78, c155, c1278] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c1503 := derived1503 a h
  have h3 : Entails.eval a c882 := derived882 a h
  have h4 : Entails.eval a c1323 := derived1323 a h
  have h5 : Entails.eval a c1510 := derived1510 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c1512 := derived1512 a h
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c1513 := derived1513 a h
  have h13 : Entails.eval a c371 := h 370 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c1240 := derived1240 a h
  have h16 : Entails.eval a c834 := derived834 a h
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c155 := h 154 (by decide)
  have h19 : Entails.eval a c1278 := derived1278 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c159, some c185, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p1515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 57) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c162, c159, c185] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c367, some c78, some c275, some c268, some c43, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 57) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c1441, c367, c78, c275, c268, c43] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1517 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c367, some c78, some c1516, some c36, some c947, some c312, some c54, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 57) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c1441, c367, c78, c1516, c36, c947, c312, c54] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c1516 := derived1516 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c947 := derived947 a h
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1514, some c65, some c368, some c367, some c1517, some c104, some c944, some c79, some c813, some c386, some c371, some c1294, some c12, some c1217, some c166, some c868, some c869, some c180, some c178, some c191, some c230, some c224, some c108, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 57) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c1441, c1514, c65, c368, c367, c1517, c104, c944, c79, c813, c386, c371, c1294, c12, c1217, c166, c868, c869, c180, c178, c191, c230, c224, c108] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1514 := derived1514 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c1517 := derived1517 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c944 := derived944 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c386 := h 385 (by decide)
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c1294 := derived1294 a h
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c1217 := derived1217 a h
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c868 := derived868 a h
  have h17 : Entails.eval a c869 := derived869 a h
  have h18 : Entails.eval a c180 := h 179 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c191 := h 190 (by decide)
  have h21 : Entails.eval a c230 := h 229 (by decide)
  have h22 : Entails.eval a c224 := h 223 (by decide)
  have h23 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1518

end CochromaticTwenty.Certificates.B16_8_0Enumerating
