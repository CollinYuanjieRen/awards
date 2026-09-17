import MerLeanExperiment.Certificates.FixedCore1.Steps2400_2499

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8381 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c443, some c423, some c426, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8381 : lratChecker f8381 p8381 = .success := by decide +kernel
theorem unsat8381 : Unsatisfiable (PosFin 65) f8381 := by
  apply lratCheckerSound f8381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8381
  · intro a ha; simp [p8381] at ha; subst a; trivial
  · exact checked8381
theorem derived8381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8381 := by
  apply localUnsat_implies_entails f8381 [c443, c423, c426] c8381 unsat8381 (by rfl) a
  have h0 : Entails.eval a c443 := h 442 (by decide)
  have h1 : Entails.eval a c423 := h 422 (by decide)
  have h2 : Entails.eval a c426 := h 425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8382 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c426, some c7976, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8382 : lratChecker f8382 p8382 = .success := by decide +kernel
theorem unsat8382 : Unsatisfiable (PosFin 65) f8382 := by
  apply lratCheckerSound f8382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8382
  · intro a ha; simp [p8382] at ha; subst a; trivial
  · exact checked8382
theorem derived8382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8382 := by
  apply localUnsat_implies_entails f8382 [c426, c7976] c8382 unsat8382 (by rfl) a
  have h0 : Entails.eval a c426 := h 425 (by decide)
  have h1 : Entails.eval a c7976 := derived7976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8383 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c483, some c462, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8383 : lratChecker f8383 p8383 = .success := by decide +kernel
theorem unsat8383 : Unsatisfiable (PosFin 65) f8383 := by
  apply lratCheckerSound f8383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8383
  · intro a ha; simp [p8383] at ha; subst a; trivial
  · exact checked8383
theorem derived8383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8383 := by
  apply localUnsat_implies_entails f8383 [c483, c462] c8383 unsat8383 (by rfl) a
  have h0 : Entails.eval a c483 := h 482 (by decide)
  have h1 : Entails.eval a c462 := h 461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8384 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨28, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8272, some c564, some c2495, some c1523, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8384 : lratChecker f8384 p8384 = .success := by decide +kernel
theorem unsat8384 : Unsatisfiable (PosFin 65) f8384 := by
  apply lratCheckerSound f8384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8384
  · intro a ha; simp [p8384] at ha; subst a; trivial
  · exact checked8384
theorem derived8384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8384 := by
  apply localUnsat_implies_entails f8384 [c8272, c564, c2495, c1523] c8384 unsat8384 (by rfl) a
  have h0 : Entails.eval a c8272 := derived8272 a h
  have h1 : Entails.eval a c564 := h 563 (by decide)
  have h2 : Entails.eval a c2495 := h 2494 (by decide)
  have h3 : Entails.eval a c1523 := h 1522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8385 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8384, some c580, some c2445, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8385 : lratChecker f8385 p8385 = .success := by decide +kernel
theorem unsat8385 : Unsatisfiable (PosFin 65) f8385 := by
  apply lratCheckerSound f8385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8385
  · intro a ha; simp [p8385] at ha; subst a; trivial
  · exact checked8385
theorem derived8385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8385 := by
  apply localUnsat_implies_entails f8385 [c8384, c580, c2445] c8385 unsat8385 (by rfl) a
  have h0 : Entails.eval a c8384 := derived8384 a h
  have h1 : Entails.eval a c580 := h 579 (by decide)
  have h2 : Entails.eval a c2445 := h 2444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8386 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8272, some c1524, some c1523, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8386 : lratChecker f8386 p8386 = .success := by decide +kernel
theorem unsat8386 : Unsatisfiable (PosFin 65) f8386 := by
  apply lratCheckerSound f8386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8386
  · intro a ha; simp [p8386] at ha; subst a; trivial
  · exact checked8386
theorem derived8386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8386 := by
  apply localUnsat_implies_entails f8386 [c8272, c1524, c1523] c8386 unsat8386 (by rfl) a
  have h0 : Entails.eval a c8272 := derived8272 a h
  have h1 : Entails.eval a c1524 := h 1523 (by decide)
  have h2 : Entails.eval a c1523 := h 1522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8387 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8381, some c426, some c8382, some c425, some c442, some c8383, some c8386, some c2445, some c1846, some c2665, some c1696, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8387 : lratChecker f8387 p8387 = .success := by decide +kernel
theorem unsat8387 : Unsatisfiable (PosFin 65) f8387 := by
  apply lratCheckerSound f8387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8387
  · intro a ha; simp [p8387] at ha; subst a; trivial
  · exact checked8387
theorem derived8387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8387 := by
  apply localUnsat_implies_entails f8387 [c8381, c426, c8382, c425, c442, c8383, c8386, c2445, c1846, c2665, c1696] c8387 unsat8387 (by rfl) a
  have h0 : Entails.eval a c8381 := derived8381 a h
  have h1 : Entails.eval a c426 := h 425 (by decide)
  have h2 : Entails.eval a c8382 := derived8382 a h
  have h3 : Entails.eval a c425 := h 424 (by decide)
  have h4 : Entails.eval a c442 := h 441 (by decide)
  have h5 : Entails.eval a c8383 := derived8383 a h
  have h6 : Entails.eval a c8386 := derived8386 a h
  have h7 : Entails.eval a c2445 := h 2444 (by decide)
  have h8 : Entails.eval a c1846 := h 1845 (by decide)
  have h9 : Entails.eval a c2665 := h 2664 (by decide)
  have h10 : Entails.eval a c1696 := h 1695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8388 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8387, some c451, some c448, some c450, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8388 : lratChecker f8388 p8388 = .success := by decide +kernel
theorem unsat8388 : Unsatisfiable (PosFin 65) f8388 := by
  apply lratCheckerSound f8388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8388
  · intro a ha; simp [p8388] at ha; subst a; trivial
  · exact checked8388
theorem derived8388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8388 := by
  apply localUnsat_implies_entails f8388 [c8387, c451, c448, c450] c8388 unsat8388 (by rfl) a
  have h0 : Entails.eval a c8387 := derived8387 a h
  have h1 : Entails.eval a c451 := h 450 (by decide)
  have h2 : Entails.eval a c448 := h 447 (by decide)
  have h3 : Entails.eval a c450 := h 449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8389 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c505, some c1556, some c1505, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8389 : lratChecker f8389 p8389 = .success := by decide +kernel
theorem unsat8389 : Unsatisfiable (PosFin 65) f8389 := by
  apply lratCheckerSound f8389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8389
  · intro a ha; simp [p8389] at ha; subst a; trivial
  · exact checked8389
theorem derived8389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8389 := by
  apply localUnsat_implies_entails f8389 [c505, c1556, c1505] c8389 unsat8389 (by rfl) a
  have h0 : Entails.eval a c505 := h 504 (by decide)
  have h1 : Entails.eval a c1556 := h 1555 (by decide)
  have h2 : Entails.eval a c1505 := h 1504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8390 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8389, some c2071, some c2042, some c2504, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8390 : lratChecker f8390 p8390 = .success := by decide +kernel
theorem unsat8390 : Unsatisfiable (PosFin 65) f8390 := by
  apply lratCheckerSound f8390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8390
  · intro a ha; simp [p8390] at ha; subst a; trivial
  · exact checked8390
theorem derived8390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8390 := by
  apply localUnsat_implies_entails f8390 [c8389, c2071, c2042, c2504] c8390 unsat8390 (by rfl) a
  have h0 : Entails.eval a c8389 := derived8389 a h
  have h1 : Entails.eval a c2071 := h 2070 (by decide)
  have h2 : Entails.eval a c2042 := h 2041 (by decide)
  have h3 : Entails.eval a c2504 := h 2503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8391 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c505, some c1505, some c1326, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8391 : lratChecker f8391 p8391 = .success := by decide +kernel
theorem unsat8391 : Unsatisfiable (PosFin 65) f8391 := by
  apply lratCheckerSound f8391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8391
  · intro a ha; simp [p8391] at ha; subst a; trivial
  · exact checked8391
theorem derived8391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8391 := by
  apply localUnsat_implies_entails f8391 [c505, c1505, c1326] c8391 unsat8391 (by rfl) a
  have h0 : Entails.eval a c505 := h 504 (by decide)
  have h1 : Entails.eval a c1505 := h 1504 (by decide)
  have h2 : Entails.eval a c1326 := h 1325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8392 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8391, some c2145, some c2179, some c8386, some c2160, some c8390, some c2071, some c1318, some c1645, some c1871, some c1515, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8392 : lratChecker f8392 p8392 = .success := by decide +kernel
theorem unsat8392 : Unsatisfiable (PosFin 65) f8392 := by
  apply lratCheckerSound f8392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8392
  · intro a ha; simp [p8392] at ha; subst a; trivial
  · exact checked8392
theorem derived8392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8392 := by
  apply localUnsat_implies_entails f8392 [c8391, c2145, c2179, c8386, c2160, c8390, c2071, c1318, c1645, c1871, c1515] c8392 unsat8392 (by rfl) a
  have h0 : Entails.eval a c8391 := derived8391 a h
  have h1 : Entails.eval a c2145 := h 2144 (by decide)
  have h2 : Entails.eval a c2179 := h 2178 (by decide)
  have h3 : Entails.eval a c8386 := derived8386 a h
  have h4 : Entails.eval a c2160 := h 2159 (by decide)
  have h5 : Entails.eval a c8390 := derived8390 a h
  have h6 : Entails.eval a c2071 := h 2070 (by decide)
  have h7 : Entails.eval a c1318 := h 1317 (by decide)
  have h8 : Entails.eval a c1645 := h 1644 (by decide)
  have h9 : Entails.eval a c1871 := h 1870 (by decide)
  have h10 : Entails.eval a c1515 := h 1514 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8393 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8388, some c8391, some c2145, some c2179, some c8177, some c8386, some c8392, some c2171, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8393 : lratChecker f8393 p8393 = .success := by decide +kernel
theorem unsat8393 : Unsatisfiable (PosFin 65) f8393 := by
  apply lratCheckerSound f8393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8393
  · intro a ha; simp [p8393] at ha; subst a; trivial
  · exact checked8393
theorem derived8393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8393 := by
  apply localUnsat_implies_entails f8393 [c8388, c8391, c2145, c2179, c8177, c8386, c8392, c2171] c8393 unsat8393 (by rfl) a
  have h0 : Entails.eval a c8388 := derived8388 a h
  have h1 : Entails.eval a c8391 := derived8391 a h
  have h2 : Entails.eval a c2145 := h 2144 (by decide)
  have h3 : Entails.eval a c2179 := h 2178 (by decide)
  have h4 : Entails.eval a c8177 := derived8177 a h
  have h5 : Entails.eval a c8386 := derived8386 a h
  have h6 : Entails.eval a c8392 := derived8392 a h
  have h7 : Entails.eval a c2171 := h 2170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8394 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2423, some c2422, some c2442, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8394 : lratChecker f8394 p8394 = .success := by decide +kernel
theorem unsat8394 : Unsatisfiable (PosFin 65) f8394 := by
  apply lratCheckerSound f8394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8394
  · intro a ha; simp [p8394] at ha; subst a; trivial
  · exact checked8394
theorem derived8394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8394 := by
  apply localUnsat_implies_entails f8394 [c2423, c2422, c2442] c8394 unsat8394 (by rfl) a
  have h0 : Entails.eval a c2423 := h 2422 (by decide)
  have h1 : Entails.eval a c2422 := h 2421 (by decide)
  have h2 : Entails.eval a c2442 := h 2441 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8395 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c636, some c640, some c7998, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p8395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8395 : lratChecker f8395 p8395 = .success := by decide +kernel
theorem unsat8395 : Unsatisfiable (PosFin 65) f8395 := by
  apply lratCheckerSound f8395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8395
  · intro a ha; simp [p8395] at ha; subst a; trivial
  · exact checked8395
theorem derived8395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8395 := by
  apply localUnsat_implies_entails f8395 [c636, c640, c7998] c8395 unsat8395 (by rfl) a
  have h0 : Entails.eval a c636 := h 635 (by decide)
  have h1 : Entails.eval a c640 := h 639 (by decide)
  have h2 : Entails.eval a c7998 := derived7998 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8396 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8393, some c8394, some c8395, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8396 : lratChecker f8396 p8396 = .success := by decide +kernel
theorem unsat8396 : Unsatisfiable (PosFin 65) f8396 := by
  apply lratCheckerSound f8396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8396
  · intro a ha; simp [p8396] at ha; subst a; trivial
  · exact checked8396
theorem derived8396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8396 := by
  apply localUnsat_implies_entails f8396 [c8393, c8394, c8395] c8396 unsat8396 (by rfl) a
  have h0 : Entails.eval a c8393 := derived8393 a h
  have h1 : Entails.eval a c8394 := derived8394 a h
  have h2 : Entails.eval a c8395 := derived8395 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8397 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c514, some c505, some c7976, some c500, some c487, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8397 : lratChecker f8397 p8397 = .success := by decide +kernel
theorem unsat8397 : Unsatisfiable (PosFin 65) f8397 := by
  apply lratCheckerSound f8397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8397
  · intro a ha; simp [p8397] at ha; subst a; trivial
  · exact checked8397
theorem derived8397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8397 := by
  apply localUnsat_implies_entails f8397 [c514, c505, c7976, c500, c487] c8397 unsat8397 (by rfl) a
  have h0 : Entails.eval a c514 := h 513 (by decide)
  have h1 : Entails.eval a c505 := h 504 (by decide)
  have h2 : Entails.eval a c7976 := derived7976 a h
  have h3 : Entails.eval a c500 := h 499 (by decide)
  have h4 : Entails.eval a c487 := h 486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8398 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8396, some c8388, some c8397, some c2180, some c8386, some c2012, some c2175, some c2124, some c2461, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8398 : lratChecker f8398 p8398 = .success := by decide +kernel
theorem unsat8398 : Unsatisfiable (PosFin 65) f8398 := by
  apply lratCheckerSound f8398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8398
  · intro a ha; simp [p8398] at ha; subst a; trivial
  · exact checked8398
theorem derived8398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8398 := by
  apply localUnsat_implies_entails f8398 [c8396, c8388, c8397, c2180, c8386, c2012, c2175, c2124, c2461] c8398 unsat8398 (by rfl) a
  have h0 : Entails.eval a c8396 := derived8396 a h
  have h1 : Entails.eval a c8388 := derived8388 a h
  have h2 : Entails.eval a c8397 := derived8397 a h
  have h3 : Entails.eval a c2180 := h 2179 (by decide)
  have h4 : Entails.eval a c8386 := derived8386 a h
  have h5 : Entails.eval a c2012 := h 2011 (by decide)
  have h6 : Entails.eval a c2175 := h 2174 (by decide)
  have h7 : Entails.eval a c2124 := h 2123 (by decide)
  have h8 : Entails.eval a c2461 := h 2460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8399 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8377, some c7849, some c8388, some c8396, some c8398, some c8395, some c2452, some c2003, some c513, some c1999, some c2054, some c2429, some c2441, some c8177, some c667, some c8272, some c1042, some c7985, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8399 : lratChecker f8399 p8399 = .success := by decide +kernel
theorem unsat8399 : Unsatisfiable (PosFin 65) f8399 := by
  apply lratCheckerSound f8399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8399
  · intro a ha; simp [p8399] at ha; subst a; trivial
  · exact checked8399
theorem derived8399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8399 := by
  apply localUnsat_implies_entails f8399 [c8380, c8377, c7849, c8388, c8396, c8398, c8395, c2452, c2003, c513, c1999, c2054, c2429, c2441, c8177, c667, c8272, c1042, c7985] c8399 unsat8399 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8388 := derived8388 a h
  have h4 : Entails.eval a c8396 := derived8396 a h
  have h5 : Entails.eval a c8398 := derived8398 a h
  have h6 : Entails.eval a c8395 := derived8395 a h
  have h7 : Entails.eval a c2452 := h 2451 (by decide)
  have h8 : Entails.eval a c2003 := h 2002 (by decide)
  have h9 : Entails.eval a c513 := h 512 (by decide)
  have h10 : Entails.eval a c1999 := h 1998 (by decide)
  have h11 : Entails.eval a c2054 := h 2053 (by decide)
  have h12 : Entails.eval a c2429 := h 2428 (by decide)
  have h13 : Entails.eval a c2441 := h 2440 (by decide)
  have h14 : Entails.eval a c8177 := derived8177 a h
  have h15 : Entails.eval a c667 := h 666 (by decide)
  have h16 : Entails.eval a c8272 := derived8272 a h
  have h17 : Entails.eval a c1042 := h 1041 (by decide)
  have h18 : Entails.eval a c7985 := derived7985 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8400 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c633, some c613, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8400 : lratChecker f8400 p8400 = .success := by decide +kernel
theorem unsat8400 : Unsatisfiable (PosFin 65) f8400 := by
  apply lratCheckerSound f8400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8400
  · intro a ha; simp [p8400] at ha; subst a; trivial
  · exact checked8400
theorem derived8400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8400 := by
  apply localUnsat_implies_entails f8400 [c633, c613] c8400 unsat8400 (by rfl) a
  have h0 : Entails.eval a c633 := h 632 (by decide)
  have h1 : Entails.eval a c613 := h 612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8401 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8381, some c426, some c425, some c8383, some c8177, some c8400, some c2496, some c2485, some c2493, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8401 : lratChecker f8401 p8401 = .success := by decide +kernel
theorem unsat8401 : Unsatisfiable (PosFin 65) f8401 := by
  apply lratCheckerSound f8401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8401
  · intro a ha; simp [p8401] at ha; subst a; trivial
  · exact checked8401
theorem derived8401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8401 := by
  apply localUnsat_implies_entails f8401 [c8381, c426, c425, c8383, c8177, c8400, c2496, c2485, c2493] c8401 unsat8401 (by rfl) a
  have h0 : Entails.eval a c8381 := derived8381 a h
  have h1 : Entails.eval a c426 := h 425 (by decide)
  have h2 : Entails.eval a c425 := h 424 (by decide)
  have h3 : Entails.eval a c8383 := derived8383 a h
  have h4 : Entails.eval a c8177 := derived8177 a h
  have h5 : Entails.eval a c8400 := derived8400 a h
  have h6 : Entails.eval a c2496 := h 2495 (by decide)
  have h7 : Entails.eval a c2485 := h 2484 (by decide)
  have h8 : Entails.eval a c2493 := h 2492 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8402 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c618, some c1992, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8402 : lratChecker f8402 p8402 = .success := by decide +kernel
theorem unsat8402 : Unsatisfiable (PosFin 65) f8402 := by
  apply lratCheckerSound f8402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8402
  · intro a ha; simp [p8402] at ha; subst a; trivial
  · exact checked8402
theorem derived8402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8402 := by
  apply localUnsat_implies_entails f8402 [c618, c1992] c8402 unsat8402 (by rfl) a
  have h0 : Entails.eval a c618 := h 617 (by decide)
  have h1 : Entails.eval a c1992 := h 1991 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8403 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8401, some c8402, some c7976, some c2179, some c8177, some c2150, some c2160, some c8400, some c2171, some c2168, some c1969, some c8272, some c1637, some c1265, some c1261, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8403 : lratChecker f8403 p8403 = .success := by decide +kernel
theorem unsat8403 : Unsatisfiable (PosFin 65) f8403 := by
  apply lratCheckerSound f8403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8403
  · intro a ha; simp [p8403] at ha; subst a; trivial
  · exact checked8403
theorem derived8403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8403 := by
  apply localUnsat_implies_entails f8403 [c8401, c8402, c7976, c2179, c8177, c2150, c2160, c8400, c2171, c2168, c1969, c8272, c1637, c1265, c1261] c8403 unsat8403 (by rfl) a
  have h0 : Entails.eval a c8401 := derived8401 a h
  have h1 : Entails.eval a c8402 := derived8402 a h
  have h2 : Entails.eval a c7976 := derived7976 a h
  have h3 : Entails.eval a c2179 := h 2178 (by decide)
  have h4 : Entails.eval a c8177 := derived8177 a h
  have h5 : Entails.eval a c2150 := h 2149 (by decide)
  have h6 : Entails.eval a c2160 := h 2159 (by decide)
  have h7 : Entails.eval a c8400 := derived8400 a h
  have h8 : Entails.eval a c2171 := h 2170 (by decide)
  have h9 : Entails.eval a c2168 := h 2167 (by decide)
  have h10 : Entails.eval a c1969 := h 1968 (by decide)
  have h11 : Entails.eval a c8272 := derived8272 a h
  have h12 : Entails.eval a c1637 := h 1636 (by decide)
  have h13 : Entails.eval a c1265 := h 1264 (by decide)
  have h14 : Entails.eval a c1261 := h 1260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8404 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8401, some c8402, some c7976, some c8403, some c8208, some c617, some c1962, some c2143, some c2155, some c1638, some c1268, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8404 : lratChecker f8404 p8404 = .success := by decide +kernel
theorem unsat8404 : Unsatisfiable (PosFin 65) f8404 := by
  apply lratCheckerSound f8404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8404
  · intro a ha; simp [p8404] at ha; subst a; trivial
  · exact checked8404
theorem derived8404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8404 := by
  apply localUnsat_implies_entails f8404 [c8401, c8402, c7976, c8403, c8208, c617, c1962, c2143, c2155, c1638, c1268] c8404 unsat8404 (by rfl) a
  have h0 : Entails.eval a c8401 := derived8401 a h
  have h1 : Entails.eval a c8402 := derived8402 a h
  have h2 : Entails.eval a c7976 := derived7976 a h
  have h3 : Entails.eval a c8403 := derived8403 a h
  have h4 : Entails.eval a c8208 := derived8208 a h
  have h5 : Entails.eval a c617 := h 616 (by decide)
  have h6 : Entails.eval a c1962 := h 1961 (by decide)
  have h7 : Entails.eval a c2143 := h 2142 (by decide)
  have h8 : Entails.eval a c2155 := h 2154 (by decide)
  have h9 : Entails.eval a c1638 := h 1637 (by decide)
  have h10 : Entails.eval a c1268 := h 1267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8405 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c451, some c448, some c450, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8405 : lratChecker f8405 p8405 = .success := by decide +kernel
theorem unsat8405 : Unsatisfiable (PosFin 65) f8405 := by
  apply lratCheckerSound f8405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8405
  · intro a ha; simp [p8405] at ha; subst a; trivial
  · exact checked8405
theorem derived8405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8405 := by
  apply localUnsat_implies_entails f8405 [c451, c448, c450] c8405 unsat8405 (by rfl) a
  have h0 : Entails.eval a c451 := h 450 (by decide)
  have h1 : Entails.eval a c448 := h 447 (by decide)
  have h2 : Entails.eval a c450 := h 449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8406 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2010, some c2000, some c8177, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8406 : lratChecker f8406 p8406 = .success := by decide +kernel
theorem unsat8406 : Unsatisfiable (PosFin 65) f8406 := by
  apply lratCheckerSound f8406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8406
  · intro a ha; simp [p8406] at ha; subst a; trivial
  · exact checked8406
theorem derived8406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8406 := by
  apply localUnsat_implies_entails f8406 [c2010, c2000, c8177] c8406 unsat8406 (by rfl) a
  have h0 : Entails.eval a c2010 := h 2009 (by decide)
  have h1 : Entails.eval a c2000 := h 1999 (by decide)
  have h2 : Entails.eval a c8177 := derived8177 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8407 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8380, some c8399, some c8404, some c8395, some c8405, some c8406, some c2015, some c513, some c1999, some c2166, some c2054, some c8177, some c2004, some c667, some c1078, some c1051, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8407 : lratChecker f8407 p8407 = .success := by decide +kernel
theorem unsat8407 : Unsatisfiable (PosFin 65) f8407 := by
  apply lratCheckerSound f8407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8407
  · intro a ha; simp [p8407] at ha; subst a; trivial
  · exact checked8407
theorem derived8407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8407 := by
  apply localUnsat_implies_entails f8407 [c8377, c7849, c8380, c8399, c8404, c8395, c8405, c8406, c2015, c513, c1999, c2166, c2054, c8177, c2004, c667, c1078, c1051] c8407 unsat8407 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8380 := derived8380 a h
  have h3 : Entails.eval a c8399 := derived8399 a h
  have h4 : Entails.eval a c8404 := derived8404 a h
  have h5 : Entails.eval a c8395 := derived8395 a h
  have h6 : Entails.eval a c8405 := derived8405 a h
  have h7 : Entails.eval a c8406 := derived8406 a h
  have h8 : Entails.eval a c2015 := h 2014 (by decide)
  have h9 : Entails.eval a c513 := h 512 (by decide)
  have h10 : Entails.eval a c1999 := h 1998 (by decide)
  have h11 : Entails.eval a c2166 := h 2165 (by decide)
  have h12 : Entails.eval a c2054 := h 2053 (by decide)
  have h13 : Entails.eval a c8177 := derived8177 a h
  have h14 : Entails.eval a c2004 := h 2003 (by decide)
  have h15 : Entails.eval a c667 := h 666 (by decide)
  have h16 : Entails.eval a c1078 := h 1077 (by decide)
  have h17 : Entails.eval a c1051 := h 1050 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8408 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8407, some c8377, some c7849, some c8378, some c7961, some c8116, some c518, some c8236, some c7982, some c2609, some c8379, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8408 : lratChecker f8408 p8408 = .success := by decide +kernel
theorem unsat8408 : Unsatisfiable (PosFin 65) f8408 := by
  apply lratCheckerSound f8408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8408
  · intro a ha; simp [p8408] at ha; subst a; trivial
  · exact checked8408
theorem derived8408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8408 := by
  apply localUnsat_implies_entails f8408 [c8407, c8377, c7849, c8378, c7961, c8116, c518, c8236, c7982, c2609, c8379] c8408 unsat8408 (by rfl) a
  have h0 : Entails.eval a c8407 := derived8407 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8378 := derived8378 a h
  have h4 : Entails.eval a c7961 := derived7961 a h
  have h5 : Entails.eval a c8116 := derived8116 a h
  have h6 : Entails.eval a c518 := h 517 (by decide)
  have h7 : Entails.eval a c8236 := derived8236 a h
  have h8 : Entails.eval a c7982 := derived7982 a h
  have h9 : Entails.eval a c2609 := h 2608 (by decide)
  have h10 : Entails.eval a c8379 := derived8379 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8409 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c505, some c7976, some c8391, some c2618, some c458, some c2660, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8409 : lratChecker f8409 p8409 = .success := by decide +kernel
theorem unsat8409 : Unsatisfiable (PosFin 65) f8409 := by
  apply lratCheckerSound f8409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8409
  · intro a ha; simp [p8409] at ha; subst a; trivial
  · exact checked8409
theorem derived8409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8409 := by
  apply localUnsat_implies_entails f8409 [c505, c7976, c8391, c2618, c458, c2660] c8409 unsat8409 (by rfl) a
  have h0 : Entails.eval a c505 := h 504 (by decide)
  have h1 : Entails.eval a c7976 := derived7976 a h
  have h2 : Entails.eval a c8391 := derived8391 a h
  have h3 : Entails.eval a c2618 := h 2617 (by decide)
  have h4 : Entails.eval a c458 := h 457 (by decide)
  have h5 : Entails.eval a c2660 := h 2659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8410 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c458, some c2660, some c1872, some c1686, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8410 : lratChecker f8410 p8410 = .success := by decide +kernel
theorem unsat8410 : Unsatisfiable (PosFin 65) f8410 := by
  apply lratCheckerSound f8410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8410
  · intro a ha; simp [p8410] at ha; subst a; trivial
  · exact checked8410
theorem derived8410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8410 := by
  apply localUnsat_implies_entails f8410 [c458, c2660, c1872, c1686] c8410 unsat8410 (by rfl) a
  have h0 : Entails.eval a c458 := h 457 (by decide)
  have h1 : Entails.eval a c2660 := h 2659 (by decide)
  have h2 : Entails.eval a c1872 := h 1871 (by decide)
  have h3 : Entails.eval a c1686 := h 1685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8411 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1477, some c8208, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8411 : lratChecker f8411 p8411 = .success := by decide +kernel
theorem unsat8411 : Unsatisfiable (PosFin 65) f8411 := by
  apply lratCheckerSound f8411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8411
  · intro a ha; simp [p8411] at ha; subst a; trivial
  · exact checked8411
theorem derived8411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8411 := by
  apply localUnsat_implies_entails f8411 [c1477, c8208] c8411 unsat8411 (by rfl) a
  have h0 : Entails.eval a c1477 := h 1476 (by decide)
  have h1 : Entails.eval a c8208 := derived8208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8412 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2609, some c1820, some c2561, some c1726, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8412 : lratChecker f8412 p8412 = .success := by decide +kernel
theorem unsat8412 : Unsatisfiable (PosFin 65) f8412 := by
  apply lratCheckerSound f8412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8412
  · intro a ha; simp [p8412] at ha; subst a; trivial
  · exact checked8412
theorem derived8412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8412 := by
  apply localUnsat_implies_entails f8412 [c2609, c1820, c2561, c1726] c8412 unsat8412 (by rfl) a
  have h0 : Entails.eval a c2609 := h 2608 (by decide)
  have h1 : Entails.eval a c1820 := h 1819 (by decide)
  have h2 : Entails.eval a c2561 := h 2560 (by decide)
  have h3 : Entails.eval a c1726 := h 1725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8413 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2586, some c1877, some c7201, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8413 : lratChecker f8413 p8413 = .success := by decide +kernel
theorem unsat8413 : Unsatisfiable (PosFin 65) f8413 := by
  apply lratCheckerSound f8413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8413
  · intro a ha; simp [p8413] at ha; subst a; trivial
  · exact checked8413
theorem derived8413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8413 := by
  apply localUnsat_implies_entails f8413 [c2586, c1877, c7201] c8413 unsat8413 (by rfl) a
  have h0 : Entails.eval a c2586 := h 2585 (by decide)
  have h1 : Entails.eval a c1877 := h 1876 (by decide)
  have h2 : Entails.eval a c7201 := derived7201 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8414 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1883, some c2592, some c1644, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8414 : lratChecker f8414 p8414 = .success := by decide +kernel
theorem unsat8414 : Unsatisfiable (PosFin 65) f8414 := by
  apply lratCheckerSound f8414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8414
  · intro a ha; simp [p8414] at ha; subst a; trivial
  · exact checked8414
theorem derived8414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8414 := by
  apply localUnsat_implies_entails f8414 [c1883, c2592, c1644] c8414 unsat8414 (by rfl) a
  have h0 : Entails.eval a c1883 := h 1882 (by decide)
  have h1 : Entails.eval a c2592 := h 2591 (by decide)
  have h2 : Entails.eval a c1644 := h 1643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8415 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8409, some c8394, some c8410, some c8383, some c8411, some c8412, some c8414, some c8386, some c1531, some c1294, some c879, some c1210, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8415 : lratChecker f8415 p8415 = .success := by decide +kernel
theorem unsat8415 : Unsatisfiable (PosFin 65) f8415 := by
  apply lratCheckerSound f8415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8415
  · intro a ha; simp [p8415] at ha; subst a; trivial
  · exact checked8415
theorem derived8415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8415 := by
  apply localUnsat_implies_entails f8415 [c8409, c8394, c8410, c8383, c8411, c8412, c8414, c8386, c1531, c1294, c879, c1210] c8415 unsat8415 (by rfl) a
  have h0 : Entails.eval a c8409 := derived8409 a h
  have h1 : Entails.eval a c8394 := derived8394 a h
  have h2 : Entails.eval a c8410 := derived8410 a h
  have h3 : Entails.eval a c8383 := derived8383 a h
  have h4 : Entails.eval a c8411 := derived8411 a h
  have h5 : Entails.eval a c8412 := derived8412 a h
  have h6 : Entails.eval a c8414 := derived8414 a h
  have h7 : Entails.eval a c8386 := derived8386 a h
  have h8 : Entails.eval a c1531 := h 1530 (by decide)
  have h9 : Entails.eval a c1294 := h 1293 (by decide)
  have h10 : Entails.eval a c879 := h 878 (by decide)
  have h11 : Entails.eval a c1210 := h 1209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8416 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c458, some c1872, some c7439, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8416 : lratChecker f8416 p8416 = .success := by decide +kernel
theorem unsat8416 : Unsatisfiable (PosFin 65) f8416 := by
  apply lratCheckerSound f8416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8416
  · intro a ha; simp [p8416] at ha; subst a; trivial
  · exact checked8416
theorem derived8416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8416 := by
  apply localUnsat_implies_entails f8416 [c458, c1872, c7439] c8416 unsat8416 (by rfl) a
  have h0 : Entails.eval a c458 := h 457 (by decide)
  have h1 : Entails.eval a c1872 := h 1871 (by decide)
  have h2 : Entails.eval a c7439 := derived7439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8417 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8208, some c1573, some c1245, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8417 : lratChecker f8417 p8417 = .success := by decide +kernel
theorem unsat8417 : Unsatisfiable (PosFin 65) f8417 := by
  apply lratCheckerSound f8417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8417
  · intro a ha; simp [p8417] at ha; subst a; trivial
  · exact checked8417
theorem derived8417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8417 := by
  apply localUnsat_implies_entails f8417 [c8208, c1573, c1245] c8417 unsat8417 (by rfl) a
  have h0 : Entails.eval a c8208 := derived8208 a h
  have h1 : Entails.eval a c1573 := h 1572 (by decide)
  have h2 : Entails.eval a c1245 := h 1244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8418 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨13, by decide⟩, false), (⟨31, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1818, some c1824, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8418 : lratChecker f8418 p8418 = .success := by decide +kernel
theorem unsat8418 : Unsatisfiable (PosFin 65) f8418 := by
  apply lratCheckerSound f8418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8418
  · intro a ha; simp [p8418] at ha; subst a; trivial
  · exact checked8418
theorem derived8418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8418 := by
  apply localUnsat_implies_entails f8418 [c1818, c1824] c8418 unsat8418 (by rfl) a
  have h0 : Entails.eval a c1818 := h 1817 (by decide)
  have h1 : Entails.eval a c1824 := h 1823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8419 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8409, some c8415, some c8418, some c1606, some c1577, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8419 : lratChecker f8419 p8419 = .success := by decide +kernel
theorem unsat8419 : Unsatisfiable (PosFin 65) f8419 := by
  apply lratCheckerSound f8419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8419
  · intro a ha; simp [p8419] at ha; subst a; trivial
  · exact checked8419
theorem derived8419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8419 := by
  apply localUnsat_implies_entails f8419 [c8409, c8415, c8418, c1606, c1577] c8419 unsat8419 (by rfl) a
  have h0 : Entails.eval a c8409 := derived8409 a h
  have h1 : Entails.eval a c8415 := derived8415 a h
  have h2 : Entails.eval a c8418 := derived8418 a h
  have h3 : Entails.eval a c1606 := h 1605 (by decide)
  have h4 : Entails.eval a c1577 := h 1576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8420 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2431, some c8410, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8420 : lratChecker f8420 p8420 = .success := by decide +kernel
theorem unsat8420 : Unsatisfiable (PosFin 65) f8420 := by
  apply lratCheckerSound f8420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8420
  · intro a ha; simp [p8420] at ha; subst a; trivial
  · exact checked8420
theorem derived8420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8420 := by
  apply localUnsat_implies_entails f8420 [c2431, c8410] c8420 unsat8420 (by rfl) a
  have h0 : Entails.eval a c2431 := h 2430 (by decide)
  have h1 : Entails.eval a c8410 := derived8410 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8421 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8419, some c8397, some c8420, some c8383, some c8411, some c8412, some c8414, some c8386, some c8385, some c1531, some c2448, some c1366, some c2554, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8421 : lratChecker f8421 p8421 = .success := by decide +kernel
theorem unsat8421 : Unsatisfiable (PosFin 65) f8421 := by
  apply lratCheckerSound f8421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8421
  · intro a ha; simp [p8421] at ha; subst a; trivial
  · exact checked8421
theorem derived8421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8421 := by
  apply localUnsat_implies_entails f8421 [c8419, c8397, c8420, c8383, c8411, c8412, c8414, c8386, c8385, c1531, c2448, c1366, c2554] c8421 unsat8421 (by rfl) a
  have h0 : Entails.eval a c8419 := derived8419 a h
  have h1 : Entails.eval a c8397 := derived8397 a h
  have h2 : Entails.eval a c8420 := derived8420 a h
  have h3 : Entails.eval a c8383 := derived8383 a h
  have h4 : Entails.eval a c8411 := derived8411 a h
  have h5 : Entails.eval a c8412 := derived8412 a h
  have h6 : Entails.eval a c8414 := derived8414 a h
  have h7 : Entails.eval a c8386 := derived8386 a h
  have h8 : Entails.eval a c8385 := derived8385 a h
  have h9 : Entails.eval a c1531 := h 1530 (by decide)
  have h10 : Entails.eval a c2448 := h 2447 (by decide)
  have h11 : Entails.eval a c1366 := h 1365 (by decide)
  have h12 : Entails.eval a c2554 := h 2553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8422 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨31, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1848, some c1824, some c1843, some c1857, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8422 : lratChecker f8422 p8422 = .success := by decide +kernel
theorem unsat8422 : Unsatisfiable (PosFin 65) f8422 := by
  apply lratCheckerSound f8422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8422
  · intro a ha; simp [p8422] at ha; subst a; trivial
  · exact checked8422
theorem derived8422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8422 := by
  apply localUnsat_implies_entails f8422 [c1848, c1824, c1843, c1857] c8422 unsat8422 (by rfl) a
  have h0 : Entails.eval a c1848 := h 1847 (by decide)
  have h1 : Entails.eval a c1824 := h 1823 (by decide)
  have h2 : Entails.eval a c1843 := h 1842 (by decide)
  have h3 : Entails.eval a c1857 := h 1856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8423 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8419, some c8397, some c8421, some c8416, some c8417, some c8383, some c8412, some c8422, some c1589, some c1603, some c1588, some c1595, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8423 : lratChecker f8423 p8423 = .success := by decide +kernel
theorem unsat8423 : Unsatisfiable (PosFin 65) f8423 := by
  apply lratCheckerSound f8423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8423
  · intro a ha; simp [p8423] at ha; subst a; trivial
  · exact checked8423
theorem derived8423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8423 := by
  apply localUnsat_implies_entails f8423 [c8419, c8397, c8421, c8416, c8417, c8383, c8412, c8422, c1589, c1603, c1588, c1595] c8423 unsat8423 (by rfl) a
  have h0 : Entails.eval a c8419 := derived8419 a h
  have h1 : Entails.eval a c8397 := derived8397 a h
  have h2 : Entails.eval a c8421 := derived8421 a h
  have h3 : Entails.eval a c8416 := derived8416 a h
  have h4 : Entails.eval a c8417 := derived8417 a h
  have h5 : Entails.eval a c8383 := derived8383 a h
  have h6 : Entails.eval a c8412 := derived8412 a h
  have h7 : Entails.eval a c8422 := derived8422 a h
  have h8 : Entails.eval a c1589 := h 1588 (by decide)
  have h9 : Entails.eval a c1603 := h 1602 (by decide)
  have h10 : Entails.eval a c1588 := h 1587 (by decide)
  have h11 : Entails.eval a c1595 := h 1594 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8424 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8391, some c2145, some c2161, some c2179, some c8392, some c8386, some c2171, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8424 : lratChecker f8424 p8424 = .success := by decide +kernel
theorem unsat8424 : Unsatisfiable (PosFin 65) f8424 := by
  apply lratCheckerSound f8424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8424
  · intro a ha; simp [p8424] at ha; subst a; trivial
  · exact checked8424
theorem derived8424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8424 := by
  apply localUnsat_implies_entails f8424 [c8391, c2145, c2161, c2179, c8392, c8386, c2171] c8424 unsat8424 (by rfl) a
  have h0 : Entails.eval a c8391 := derived8391 a h
  have h1 : Entails.eval a c2145 := h 2144 (by decide)
  have h2 : Entails.eval a c2161 := h 2160 (by decide)
  have h3 : Entails.eval a c2179 := h 2178 (by decide)
  have h4 : Entails.eval a c8392 := derived8392 a h
  have h5 : Entails.eval a c8386 := derived8386 a h
  have h6 : Entails.eval a c2171 := h 2170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8425 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8423, some c8424, some c8397, some c2180, some c8386, some c1531, some c2175, some c8208, some c1318, some c2609, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8425 : lratChecker f8425 p8425 = .success := by decide +kernel
theorem unsat8425 : Unsatisfiable (PosFin 65) f8425 := by
  apply lratCheckerSound f8425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8425
  · intro a ha; simp [p8425] at ha; subst a; trivial
  · exact checked8425
theorem derived8425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8425 := by
  apply localUnsat_implies_entails f8425 [c8423, c8424, c8397, c2180, c8386, c1531, c2175, c8208, c1318, c2609] c8425 unsat8425 (by rfl) a
  have h0 : Entails.eval a c8423 := derived8423 a h
  have h1 : Entails.eval a c8424 := derived8424 a h
  have h2 : Entails.eval a c8397 := derived8397 a h
  have h3 : Entails.eval a c2180 := h 2179 (by decide)
  have h4 : Entails.eval a c8386 := derived8386 a h
  have h5 : Entails.eval a c1531 := h 1530 (by decide)
  have h6 : Entails.eval a c2175 := h 2174 (by decide)
  have h7 : Entails.eval a c8208 := derived8208 a h
  have h8 : Entails.eval a c1318 := h 1317 (by decide)
  have h9 : Entails.eval a c2609 := h 2608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8426 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨31, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c505, some c7976, some c2618, some c2111, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8426 : lratChecker f8426 p8426 = .success := by decide +kernel
theorem unsat8426 : Unsatisfiable (PosFin 65) f8426 := by
  apply lratCheckerSound f8426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8426
  · intro a ha; simp [p8426] at ha; subst a; trivial
  · exact checked8426
theorem derived8426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8426 := by
  apply localUnsat_implies_entails f8426 [c505, c7976, c2618, c2111] c8426 unsat8426 (by rfl) a
  have h0 : Entails.eval a c505 := h 504 (by decide)
  have h1 : Entails.eval a c7976 := derived7976 a h
  have h2 : Entails.eval a c2618 := h 2617 (by decide)
  have h3 : Entails.eval a c2111 := h 2110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8427 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8425, some c8423, some c8426, some c2145, some c8418, some c2179, some c7439, some c7375, some c2171, some c1637, some c2079, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8427 : lratChecker f8427 p8427 = .success := by decide +kernel
theorem unsat8427 : Unsatisfiable (PosFin 65) f8427 := by
  apply lratCheckerSound f8427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8427
  · intro a ha; simp [p8427] at ha; subst a; trivial
  · exact checked8427
theorem derived8427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8427 := by
  apply localUnsat_implies_entails f8427 [c8425, c8423, c8426, c2145, c8418, c2179, c7439, c7375, c2171, c1637, c2079] c8427 unsat8427 (by rfl) a
  have h0 : Entails.eval a c8425 := derived8425 a h
  have h1 : Entails.eval a c8423 := derived8423 a h
  have h2 : Entails.eval a c8426 := derived8426 a h
  have h3 : Entails.eval a c2145 := h 2144 (by decide)
  have h4 : Entails.eval a c8418 := derived8418 a h
  have h5 : Entails.eval a c2179 := h 2178 (by decide)
  have h6 : Entails.eval a c7439 := derived7439 a h
  have h7 : Entails.eval a c7375 := derived7375 a h
  have h8 : Entails.eval a c2171 := h 2170 (by decide)
  have h9 : Entails.eval a c1637 := h 1636 (by decide)
  have h10 : Entails.eval a c2079 := h 2078 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8428 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨31, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2151, some c2154, some c2165, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p8428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8428 : lratChecker f8428 p8428 = .success := by decide +kernel
theorem unsat8428 : Unsatisfiable (PosFin 65) f8428 := by
  apply lratCheckerSound f8428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8428
  · intro a ha; simp [p8428] at ha; subst a; trivial
  · exact checked8428
theorem derived8428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8428 := by
  apply localUnsat_implies_entails f8428 [c2151, c2154, c2165] c8428 unsat8428 (by rfl) a
  have h0 : Entails.eval a c2151 := h 2150 (by decide)
  have h1 : Entails.eval a c2154 := h 2153 (by decide)
  have h2 : Entails.eval a c2165 := h 2164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8429 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8423, some c8427, some c8397, some c2180, some c8428, some c8412, some c2169, some c2175, some c2144, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8429 : lratChecker f8429 p8429 = .success := by decide +kernel
theorem unsat8429 : Unsatisfiable (PosFin 65) f8429 := by
  apply lratCheckerSound f8429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8429
  · intro a ha; simp [p8429] at ha; subst a; trivial
  · exact checked8429
theorem derived8429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8429 := by
  apply localUnsat_implies_entails f8429 [c8423, c8427, c8397, c2180, c8428, c8412, c2169, c2175, c2144] c8429 unsat8429 (by rfl) a
  have h0 : Entails.eval a c8423 := derived8423 a h
  have h1 : Entails.eval a c8427 := derived8427 a h
  have h2 : Entails.eval a c8397 := derived8397 a h
  have h3 : Entails.eval a c2180 := h 2179 (by decide)
  have h4 : Entails.eval a c8428 := derived8428 a h
  have h5 : Entails.eval a c8412 := derived8412 a h
  have h6 : Entails.eval a c2169 := h 2168 (by decide)
  have h7 : Entails.eval a c2175 := h 2174 (by decide)
  have h8 : Entails.eval a c2144 := h 2143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8430 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8429, some c8394, some c8152, some c8413, some c1471, some c8208, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8430 : lratChecker f8430 p8430 = .success := by decide +kernel
theorem unsat8430 : Unsatisfiable (PosFin 65) f8430 := by
  apply lratCheckerSound f8430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8430
  · intro a ha; simp [p8430] at ha; subst a; trivial
  · exact checked8430
theorem derived8430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8430 := by
  apply localUnsat_implies_entails f8430 [c8429, c8394, c8152, c8413, c1471, c8208] c8430 unsat8430 (by rfl) a
  have h0 : Entails.eval a c8429 := derived8429 a h
  have h1 : Entails.eval a c8394 := derived8394 a h
  have h2 : Entails.eval a c8152 := derived8152 a h
  have h3 : Entails.eval a c8413 := derived8413 a h
  have h4 : Entails.eval a c1471 := h 1470 (by decide)
  have h5 : Entails.eval a c8208 := derived8208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8431 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨24, by decide⟩, false), (⟨31, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c497, some c495, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8431 : lratChecker f8431 p8431 = .success := by decide +kernel
theorem unsat8431 : Unsatisfiable (PosFin 65) f8431 := by
  apply lratCheckerSound f8431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8431
  · intro a ha; simp [p8431] at ha; subst a; trivial
  · exact checked8431
theorem derived8431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8431 := by
  apply localUnsat_implies_entails f8431 [c497, c495] c8431 unsat8431 (by rfl) a
  have h0 : Entails.eval a c497 := h 496 (by decide)
  have h1 : Entails.eval a c495 := h 494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8432 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1605, some c1862, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8432 : lratChecker f8432 p8432 = .success := by decide +kernel
theorem unsat8432 : Unsatisfiable (PosFin 65) f8432 := by
  apply lratCheckerSound f8432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8432
  · intro a ha; simp [p8432] at ha; subst a; trivial
  · exact checked8432
theorem derived8432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8432 := by
  apply localUnsat_implies_entails f8432 [c1605, c1862] c8432 unsat8432 (by rfl) a
  have h0 : Entails.eval a c1605 := h 1604 (by decide)
  have h1 : Entails.eval a c1862 := h 1861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8433 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8429, some c7929, some c8430, some c8417, some c8431, some c8432, some c1883, some c1644, some c984, some c1105, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8433 : lratChecker f8433 p8433 = .success := by decide +kernel
theorem unsat8433 : Unsatisfiable (PosFin 65) f8433 := by
  apply lratCheckerSound f8433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8433
  · intro a ha; simp [p8433] at ha; subst a; trivial
  · exact checked8433
theorem derived8433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8433 := by
  apply localUnsat_implies_entails f8433 [c8429, c7929, c8430, c8417, c8431, c8432, c1883, c1644, c984, c1105] c8433 unsat8433 (by rfl) a
  have h0 : Entails.eval a c8429 := derived8429 a h
  have h1 : Entails.eval a c7929 := derived7929 a h
  have h2 : Entails.eval a c8430 := derived8430 a h
  have h3 : Entails.eval a c8417 := derived8417 a h
  have h4 : Entails.eval a c8431 := derived8431 a h
  have h5 : Entails.eval a c8432 := derived8432 a h
  have h6 : Entails.eval a c1883 := h 1882 (by decide)
  have h7 : Entails.eval a c1644 := h 1643 (by decide)
  have h8 : Entails.eval a c984 := h 983 (by decide)
  have h9 : Entails.eval a c1105 := h 1104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8434 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1471, some c8208, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8434 : lratChecker f8434 p8434 = .success := by decide +kernel
theorem unsat8434 : Unsatisfiable (PosFin 65) f8434 := by
  apply lratCheckerSound f8434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8434
  · intro a ha; simp [p8434] at ha; subst a; trivial
  · exact checked8434
theorem derived8434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8434 := by
  apply localUnsat_implies_entails f8434 [c1471, c8208] c8434 unsat8434 (by rfl) a
  have h0 : Entails.eval a c1471 := h 1470 (by decide)
  have h1 : Entails.eval a c8208 := derived8208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8435 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8429, some c8434, some c8413, some c8414, some c2489, some c567, some c513, some c2577, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8435 : lratChecker f8435 p8435 = .success := by decide +kernel
theorem unsat8435 : Unsatisfiable (PosFin 65) f8435 := by
  apply lratCheckerSound f8435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8435
  · intro a ha; simp [p8435] at ha; subst a; trivial
  · exact checked8435
theorem derived8435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8435 := by
  apply localUnsat_implies_entails f8435 [c8429, c8434, c8413, c8414, c2489, c567, c513, c2577] c8435 unsat8435 (by rfl) a
  have h0 : Entails.eval a c8429 := derived8429 a h
  have h1 : Entails.eval a c8434 := derived8434 a h
  have h2 : Entails.eval a c8413 := derived8413 a h
  have h3 : Entails.eval a c8414 := derived8414 a h
  have h4 : Entails.eval a c2489 := h 2488 (by decide)
  have h5 : Entails.eval a c567 := h 566 (by decide)
  have h6 : Entails.eval a c513 := h 512 (by decide)
  have h7 : Entails.eval a c2577 := h 2576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8436 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8429, some c7929, some c8433, some c8435, some c8417, some c8432, some c1883, some c1607, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8436 : lratChecker f8436 p8436 = .success := by decide +kernel
theorem unsat8436 : Unsatisfiable (PosFin 65) f8436 := by
  apply lratCheckerSound f8436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8436
  · intro a ha; simp [p8436] at ha; subst a; trivial
  · exact checked8436
theorem derived8436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8436 := by
  apply localUnsat_implies_entails f8436 [c8429, c7929, c8433, c8435, c8417, c8432, c1883, c1607] c8436 unsat8436 (by rfl) a
  have h0 : Entails.eval a c8429 := derived8429 a h
  have h1 : Entails.eval a c7929 := derived7929 a h
  have h2 : Entails.eval a c8433 := derived8433 a h
  have h3 : Entails.eval a c8435 := derived8435 a h
  have h4 : Entails.eval a c8417 := derived8417 a h
  have h5 : Entails.eval a c8432 := derived8432 a h
  have h6 : Entails.eval a c1883 := h 1882 (by decide)
  have h7 : Entails.eval a c1607 := h 1606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8437 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8394, some c8431, some c8152, some c2161, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8437 : lratChecker f8437 p8437 = .success := by decide +kernel
theorem unsat8437 : Unsatisfiable (PosFin 65) f8437 := by
  apply lratCheckerSound f8437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8437
  · intro a ha; simp [p8437] at ha; subst a; trivial
  · exact checked8437
theorem derived8437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8437 := by
  apply localUnsat_implies_entails f8437 [c8394, c8431, c8152, c2161] c8437 unsat8437 (by rfl) a
  have h0 : Entails.eval a c8394 := derived8394 a h
  have h1 : Entails.eval a c8431 := derived8431 a h
  have h2 : Entails.eval a c8152 := derived8152 a h
  have h3 : Entails.eval a c2161 := h 2160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8438 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨31, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c514, some c513, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8438 : lratChecker f8438 p8438 = .success := by decide +kernel
theorem unsat8438 : Unsatisfiable (PosFin 65) f8438 := by
  apply lratCheckerSound f8438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8438
  · intro a ha; simp [p8438] at ha; subst a; trivial
  · exact checked8438
theorem derived8438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8438 := by
  apply localUnsat_implies_entails f8438 [c514, c513] c8438 unsat8438 (by rfl) a
  have h0 : Entails.eval a c514 := h 513 (by decide)
  have h1 : Entails.eval a c513 := h 512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8439 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8436, some c8429, some c8434, some c8437, some c8438, some c2180, some c2161, some c2162, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8439 : lratChecker f8439 p8439 = .success := by decide +kernel
theorem unsat8439 : Unsatisfiable (PosFin 65) f8439 := by
  apply lratCheckerSound f8439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8439
  · intro a ha; simp [p8439] at ha; subst a; trivial
  · exact checked8439
theorem derived8439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8439 := by
  apply localUnsat_implies_entails f8439 [c8436, c8429, c8434, c8437, c8438, c2180, c2161, c2162] c8439 unsat8439 (by rfl) a
  have h0 : Entails.eval a c8436 := derived8436 a h
  have h1 : Entails.eval a c8429 := derived8429 a h
  have h2 : Entails.eval a c8434 := derived8434 a h
  have h3 : Entails.eval a c8437 := derived8437 a h
  have h4 : Entails.eval a c8438 := derived8438 a h
  have h5 : Entails.eval a c2180 := h 2179 (by decide)
  have h6 : Entails.eval a c2161 := h 2160 (by decide)
  have h7 : Entails.eval a c2162 := h 2161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8440 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨31, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2145, some c2106, some c2635, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8440 : lratChecker f8440 p8440 = .success := by decide +kernel
theorem unsat8440 : Unsatisfiable (PosFin 65) f8440 := by
  apply lratCheckerSound f8440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8440
  · intro a ha; simp [p8440] at ha; subst a; trivial
  · exact checked8440
theorem derived8440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8440 := by
  apply localUnsat_implies_entails f8440 [c2145, c2106, c2635] c8440 unsat8440 (by rfl) a
  have h0 : Entails.eval a c2145 := h 2144 (by decide)
  have h1 : Entails.eval a c2106 := h 2105 (by decide)
  have h2 : Entails.eval a c2635 := h 2634 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8441 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8440, some c8431, some c2163, some c2161, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8441 : lratChecker f8441 p8441 = .success := by decide +kernel
theorem unsat8441 : Unsatisfiable (PosFin 65) f8441 := by
  apply lratCheckerSound f8441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8441
  · intro a ha; simp [p8441] at ha; subst a; trivial
  · exact checked8441
theorem derived8441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8441 := by
  apply localUnsat_implies_entails f8441 [c8440, c8431, c2163, c2161] c8441 unsat8441 (by rfl) a
  have h0 : Entails.eval a c8440 := derived8440 a h
  have h1 : Entails.eval a c8431 := derived8431 a h
  have h2 : Entails.eval a c2163 := h 2162 (by decide)
  have h3 : Entails.eval a c2161 := h 2160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8442 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8429, some c8436, some c8439, some c8441, some c8438, some c2180, some c2577, some c1827, some c1750, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8442 : lratChecker f8442 p8442 = .success := by decide +kernel
theorem unsat8442 : Unsatisfiable (PosFin 65) f8442 := by
  apply lratCheckerSound f8442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8442
  · intro a ha; simp [p8442] at ha; subst a; trivial
  · exact checked8442
theorem derived8442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8442 := by
  apply localUnsat_implies_entails f8442 [c8429, c8436, c8439, c8441, c8438, c2180, c2577, c1827, c1750] c8442 unsat8442 (by rfl) a
  have h0 : Entails.eval a c8429 := derived8429 a h
  have h1 : Entails.eval a c8436 := derived8436 a h
  have h2 : Entails.eval a c8439 := derived8439 a h
  have h3 : Entails.eval a c8441 := derived8441 a h
  have h4 : Entails.eval a c8438 := derived8438 a h
  have h5 : Entails.eval a c2180 := h 2179 (by decide)
  have h6 : Entails.eval a c2577 := h 2576 (by decide)
  have h7 : Entails.eval a c1827 := h 1826 (by decide)
  have h8 : Entails.eval a c1750 := h 1749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8443 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8407, some c8408, some c8442, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8443 : lratChecker f8443 p8443 = .success := by decide +kernel
theorem unsat8443 : Unsatisfiable (PosFin 65) f8443 := by
  apply lratCheckerSound f8443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8443
  · intro a ha; simp [p8443] at ha; subst a; trivial
  · exact checked8443
theorem derived8443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8443 := by
  apply localUnsat_implies_entails f8443 [c8377, c7849, c8407, c8408, c8442] c8443 unsat8443 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8407 := derived8407 a h
  have h3 : Entails.eval a c8408 := derived8408 a h
  have h4 : Entails.eval a c8442 := derived8442 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8444 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c852, some c841, some c836, some c846, some c617, some c425, some c1899, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8444 : lratChecker f8444 p8444 = .success := by decide +kernel
theorem unsat8444 : Unsatisfiable (PosFin 65) f8444 := by
  apply lratCheckerSound f8444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8444
  · intro a ha; simp [p8444] at ha; subst a; trivial
  · exact checked8444
theorem derived8444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8444 := by
  apply localUnsat_implies_entails f8444 [c852, c841, c836, c846, c617, c425, c1899] c8444 unsat8444 (by rfl) a
  have h0 : Entails.eval a c852 := h 851 (by decide)
  have h1 : Entails.eval a c841 := h 840 (by decide)
  have h2 : Entails.eval a c836 := h 835 (by decide)
  have h3 : Entails.eval a c846 := h 845 (by decide)
  have h4 : Entails.eval a c617 := h 616 (by decide)
  have h5 : Entails.eval a c425 := h 424 (by decide)
  have h6 : Entails.eval a c1899 := h 1898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8445 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8395, some c8405, some c1918, some c1922, some c1920, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8445 : lratChecker f8445 p8445 = .success := by decide +kernel
theorem unsat8445 : Unsatisfiable (PosFin 65) f8445 := by
  apply lratCheckerSound f8445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8445
  · intro a ha; simp [p8445] at ha; subst a; trivial
  · exact checked8445
theorem derived8445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8445 := by
  apply localUnsat_implies_entails f8445 [c8395, c8405, c1918, c1922, c1920] c8445 unsat8445 (by rfl) a
  have h0 : Entails.eval a c8395 := derived8395 a h
  have h1 : Entails.eval a c8405 := derived8405 a h
  have h2 : Entails.eval a c1918 := h 1917 (by decide)
  have h3 : Entails.eval a c1922 := h 1921 (by decide)
  have h4 : Entails.eval a c1920 := h 1919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8446 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8394, some c633, some c2468, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8446 : lratChecker f8446 p8446 = .success := by decide +kernel
theorem unsat8446 : Unsatisfiable (PosFin 65) f8446 := by
  apply lratCheckerSound f8446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8446
  · intro a ha; simp [p8446] at ha; subst a; trivial
  · exact checked8446
theorem derived8446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8446 := by
  apply localUnsat_implies_entails f8446 [c8394, c633, c2468] c8446 unsat8446 (by rfl) a
  have h0 : Entails.eval a c8394 := derived8394 a h
  have h1 : Entails.eval a c633 := h 632 (by decide)
  have h2 : Entails.eval a c2468 := h 2467 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8447 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c617, some c1899, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8447 : lratChecker f8447 p8447 = .success := by decide +kernel
theorem unsat8447 : Unsatisfiable (PosFin 65) f8447 := by
  apply lratCheckerSound f8447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8447
  · intro a ha; simp [p8447] at ha; subst a; trivial
  · exact checked8447
theorem derived8447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8447 := by
  apply localUnsat_implies_entails f8447 [c617, c1899] c8447 unsat8447 (by rfl) a
  have h0 : Entails.eval a c617 := h 616 (by decide)
  have h1 : Entails.eval a c1899 := h 1898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8448 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8445, some c8444, some c8401, some c8402, some c8447, some c8177, some c8400, some c2012, some c1897, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8448 : lratChecker f8448 p8448 = .success := by decide +kernel
theorem unsat8448 : Unsatisfiable (PosFin 65) f8448 := by
  apply lratCheckerSound f8448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8448
  · intro a ha; simp [p8448] at ha; subst a; trivial
  · exact checked8448
theorem derived8448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8448 := by
  apply localUnsat_implies_entails f8448 [c8445, c8444, c8401, c8402, c8447, c8177, c8400, c2012, c1897] c8448 unsat8448 (by rfl) a
  have h0 : Entails.eval a c8445 := derived8445 a h
  have h1 : Entails.eval a c8444 := derived8444 a h
  have h2 : Entails.eval a c8401 := derived8401 a h
  have h3 : Entails.eval a c8402 := derived8402 a h
  have h4 : Entails.eval a c8447 := derived8447 a h
  have h5 : Entails.eval a c8177 := derived8177 a h
  have h6 : Entails.eval a c8400 := derived8400 a h
  have h7 : Entails.eval a c2012 := h 2011 (by decide)
  have h8 : Entails.eval a c1897 := h 1896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8449 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2338, some c2318, some c2325, some c2321, some c2329, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8449 : lratChecker f8449 p8449 = .success := by decide +kernel
theorem unsat8449 : Unsatisfiable (PosFin 65) f8449 := by
  apply lratCheckerSound f8449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8449
  · intro a ha; simp [p8449] at ha; subst a; trivial
  · exact checked8449
theorem derived8449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8449 := by
  apply localUnsat_implies_entails f8449 [c2338, c2318, c2325, c2321, c2329] c8449 unsat8449 (by rfl) a
  have h0 : Entails.eval a c2338 := h 2337 (by decide)
  have h1 : Entails.eval a c2318 := h 2317 (by decide)
  have h2 : Entails.eval a c2325 := h 2324 (by decide)
  have h3 : Entails.eval a c2321 := h 2320 (by decide)
  have h4 : Entails.eval a c2329 := h 2328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8450 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8237, some c1569, some c2082, some c1851, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8450 : lratChecker f8450 p8450 = .success := by decide +kernel
theorem unsat8450 : Unsatisfiable (PosFin 65) f8450 := by
  apply lratCheckerSound f8450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8450
  · intro a ha; simp [p8450] at ha; subst a; trivial
  · exact checked8450
theorem derived8450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8450 := by
  apply localUnsat_implies_entails f8450 [c8237, c1569, c2082, c1851] c8450 unsat8450 (by rfl) a
  have h0 : Entails.eval a c8237 := derived8237 a h
  have h1 : Entails.eval a c1569 := h 1568 (by decide)
  have h2 : Entails.eval a c2082 := h 2081 (by decide)
  have h3 : Entails.eval a c1851 := h 1850 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8451 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c671, some c2249, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8451 : lratChecker f8451 p8451 = .success := by decide +kernel
theorem unsat8451 : Unsatisfiable (PosFin 65) f8451 := by
  apply lratCheckerSound f8451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8451
  · intro a ha; simp [p8451] at ha; subst a; trivial
  · exact checked8451
theorem derived8451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8451 := by
  apply localUnsat_implies_entails f8451 [c671, c2249] c8451 unsat8451 (by rfl) a
  have h0 : Entails.eval a c671 := h 670 (by decide)
  have h1 : Entails.eval a c2249 := h 2248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8452 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨31, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8450, some c8229, some c8230, some c598, some c590, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8452 : lratChecker f8452 p8452 = .success := by decide +kernel
theorem unsat8452 : Unsatisfiable (PosFin 65) f8452 := by
  apply lratCheckerSound f8452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8452
  · intro a ha; simp [p8452] at ha; subst a; trivial
  · exact checked8452
theorem derived8452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8452 := by
  apply localUnsat_implies_entails f8452 [c8450, c8229, c8230, c598, c590] c8452 unsat8452 (by rfl) a
  have h0 : Entails.eval a c8450 := derived8450 a h
  have h1 : Entails.eval a c8229 := derived8229 a h
  have h2 : Entails.eval a c8230 := derived8230 a h
  have h3 : Entails.eval a c598 := h 597 (by decide)
  have h4 : Entails.eval a c590 := h 589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8453 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1897, some c1921, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8453 : lratChecker f8453 p8453 = .success := by decide +kernel
theorem unsat8453 : Unsatisfiable (PosFin 65) f8453 := by
  apply lratCheckerSound f8453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8453
  · intro a ha; simp [p8453] at ha; subst a; trivial
  · exact checked8453
theorem derived8453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8453 := by
  apply localUnsat_implies_entails f8453 [c1897, c1921] c8453 unsat8453 (by rfl) a
  have h0 : Entails.eval a c1897 := h 1896 (by decide)
  have h1 : Entails.eval a c1921 := h 1920 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8454 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1942, some c1673, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8454 : lratChecker f8454 p8454 = .success := by decide +kernel
theorem unsat8454 : Unsatisfiable (PosFin 65) f8454 := by
  apply lratCheckerSound f8454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8454
  · intro a ha; simp [p8454] at ha; subst a; trivial
  · exact checked8454
theorem derived8454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8454 := by
  apply localUnsat_implies_entails f8454 [c1942, c1673] c8454 unsat8454 (by rfl) a
  have h0 : Entails.eval a c1942 := h 1941 (by decide)
  have h1 : Entails.eval a c1673 := h 1672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8455 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c690, some c1956, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8455 : lratChecker f8455 p8455 = .success := by decide +kernel
theorem unsat8455 : Unsatisfiable (PosFin 65) f8455 := by
  apply lratCheckerSound f8455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8455
  · intro a ha; simp [p8455] at ha; subst a; trivial
  · exact checked8455
theorem derived8455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8455 := by
  apply localUnsat_implies_entails f8455 [c690, c1956] c8455 unsat8455 (by rfl) a
  have h0 : Entails.eval a c690 := h 689 (by decide)
  have h1 : Entails.eval a c1956 := h 1955 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8456 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8443, some c8448, some c8449, some c8450, some c8229, some c8451, some c8453, some c8455, some c1942, some c564, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8456 : lratChecker f8456 p8456 = .success := by decide +kernel
theorem unsat8456 : Unsatisfiable (PosFin 65) f8456 := by
  apply lratCheckerSound f8456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8456
  · intro a ha; simp [p8456] at ha; subst a; trivial
  · exact checked8456
theorem derived8456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8456 := by
  apply localUnsat_implies_entails f8456 [c7849, c8377, c8443, c8448, c8449, c8450, c8229, c8451, c8453, c8455, c1942, c564] c8456 unsat8456 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8443 := derived8443 a h
  have h3 : Entails.eval a c8448 := derived8448 a h
  have h4 : Entails.eval a c8449 := derived8449 a h
  have h5 : Entails.eval a c8450 := derived8450 a h
  have h6 : Entails.eval a c8229 := derived8229 a h
  have h7 : Entails.eval a c8451 := derived8451 a h
  have h8 : Entails.eval a c8453 := derived8453 a h
  have h9 : Entails.eval a c8455 := derived8455 a h
  have h10 : Entails.eval a c1942 := h 1941 (by decide)
  have h11 : Entails.eval a c564 := h 563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8457 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2370, some c2403, some c2401, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8457 : lratChecker f8457 p8457 = .success := by decide +kernel
theorem unsat8457 : Unsatisfiable (PosFin 65) f8457 := by
  apply lratCheckerSound f8457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8457
  · intro a ha; simp [p8457] at ha; subst a; trivial
  · exact checked8457
theorem derived8457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8457 := by
  apply localUnsat_implies_entails f8457 [c2370, c2403, c2401] c8457 unsat8457 (by rfl) a
  have h0 : Entails.eval a c2370 := h 2369 (by decide)
  have h1 : Entails.eval a c2403 := h 2402 (by decide)
  have h2 : Entails.eval a c2401 := h 2400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8458 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2341, some c8229, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8458 : lratChecker f8458 p8458 = .success := by decide +kernel
theorem unsat8458 : Unsatisfiable (PosFin 65) f8458 := by
  apply lratCheckerSound f8458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8458
  · intro a ha; simp [p8458] at ha; subst a; trivial
  · exact checked8458
theorem derived8458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8458 := by
  apply localUnsat_implies_entails f8458 [c2341, c8229] c8458 unsat8458 (by rfl) a
  have h0 : Entails.eval a c2341 := h 2340 (by decide)
  have h1 : Entails.eval a c8229 := derived8229 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8459 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2344, some c2342, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8459 : lratChecker f8459 p8459 = .success := by decide +kernel
theorem unsat8459 : Unsatisfiable (PosFin 65) f8459 := by
  apply lratCheckerSound f8459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8459
  · intro a ha; simp [p8459] at ha; subst a; trivial
  · exact checked8459
theorem derived8459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8459 := by
  apply localUnsat_implies_entails f8459 [c2344, c2342] c8459 unsat8459 (by rfl) a
  have h0 : Entails.eval a c2344 := h 2343 (by decide)
  have h1 : Entails.eval a c2342 := h 2341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8460 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8443, some c8448, some c8456, some c8457, some c7929, some c8458, some c8453, some c8459, some c8230, some c8152, some c8233, some c2262, some c675, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8460 : lratChecker f8460 p8460 = .success := by decide +kernel
theorem unsat8460 : Unsatisfiable (PosFin 65) f8460 := by
  apply lratCheckerSound f8460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8460
  · intro a ha; simp [p8460] at ha; subst a; trivial
  · exact checked8460
theorem derived8460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8460 := by
  apply localUnsat_implies_entails f8460 [c7849, c8377, c8443, c8448, c8456, c8457, c7929, c8458, c8453, c8459, c8230, c8152, c8233, c2262, c675] c8460 unsat8460 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8443 := derived8443 a h
  have h3 : Entails.eval a c8448 := derived8448 a h
  have h4 : Entails.eval a c8456 := derived8456 a h
  have h5 : Entails.eval a c8457 := derived8457 a h
  have h6 : Entails.eval a c7929 := derived7929 a h
  have h7 : Entails.eval a c8458 := derived8458 a h
  have h8 : Entails.eval a c8453 := derived8453 a h
  have h9 : Entails.eval a c8459 := derived8459 a h
  have h10 : Entails.eval a c8230 := derived8230 a h
  have h11 : Entails.eval a c8152 := derived8152 a h
  have h12 : Entails.eval a c8233 := derived8233 a h
  have h13 : Entails.eval a c2262 := h 2261 (by decide)
  have h14 : Entails.eval a c675 := h 674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8461 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c8443, some c7849, some c8448, some c8449, some c8450, some c8229, some c8453, some c8460, some c8452, some c8418, some c7439, some c7375, some c8454, some c2171, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8461 : lratChecker f8461 p8461 = .success := by decide +kernel
theorem unsat8461 : Unsatisfiable (PosFin 65) f8461 := by
  apply lratCheckerSound f8461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8461
  · intro a ha; simp [p8461] at ha; subst a; trivial
  · exact checked8461
theorem derived8461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8461 := by
  apply localUnsat_implies_entails f8461 [c8377, c8443, c7849, c8448, c8449, c8450, c8229, c8453, c8460, c8452, c8418, c7439, c7375, c8454, c2171] c8461 unsat8461 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c8443 := derived8443 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8448 := derived8448 a h
  have h4 : Entails.eval a c8449 := derived8449 a h
  have h5 : Entails.eval a c8450 := derived8450 a h
  have h6 : Entails.eval a c8229 := derived8229 a h
  have h7 : Entails.eval a c8453 := derived8453 a h
  have h8 : Entails.eval a c8460 := derived8460 a h
  have h9 : Entails.eval a c8452 := derived8452 a h
  have h10 : Entails.eval a c8418 := derived8418 a h
  have h11 : Entails.eval a c7439 := derived7439 a h
  have h12 : Entails.eval a c7375 := derived7375 a h
  have h13 : Entails.eval a c8454 := derived8454 a h
  have h14 : Entails.eval a c2171 := h 2170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8462 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c560, some c2249, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8462 : lratChecker f8462 p8462 = .success := by decide +kernel
theorem unsat8462 : Unsatisfiable (PosFin 65) f8462 := by
  apply lratCheckerSound f8462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8462
  · intro a ha; simp [p8462] at ha; subst a; trivial
  · exact checked8462
theorem derived8462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8462 := by
  apply localUnsat_implies_entails f8462 [c560, c2249] c8462 unsat8462 (by rfl) a
  have h0 : Entails.eval a c560 := h 559 (by decide)
  have h1 : Entails.eval a c2249 := h 2248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8463 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c598, some c584, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8463 : lratChecker f8463 p8463 = .success := by decide +kernel
theorem unsat8463 : Unsatisfiable (PosFin 65) f8463 := by
  apply lratCheckerSound f8463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8463
  · intro a ha; simp [p8463] at ha; subst a; trivial
  · exact checked8463
theorem derived8463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8463 := by
  apply localUnsat_implies_entails f8463 [c598, c584] c8463 unsat8463 (by rfl) a
  have h0 : Entails.eval a c598 := h 597 (by decide)
  have h1 : Entails.eval a c584 := h 583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8464 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8460, some c7849, some c8377, some c8443, some c8448, some c8449, some c8450, some c8229, some c8453, some c8230, some c8461, some c8462, some c8463, some c2180, some c2150, some c2160, some c2169, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8464 : lratChecker f8464 p8464 = .success := by decide +kernel
theorem unsat8464 : Unsatisfiable (PosFin 65) f8464 := by
  apply lratCheckerSound f8464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8464
  · intro a ha; simp [p8464] at ha; subst a; trivial
  · exact checked8464
theorem derived8464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8464 := by
  apply localUnsat_implies_entails f8464 [c8460, c7849, c8377, c8443, c8448, c8449, c8450, c8229, c8453, c8230, c8461, c8462, c8463, c2180, c2150, c2160, c2169] c8464 unsat8464 (by rfl) a
  have h0 : Entails.eval a c8460 := derived8460 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c8443 := derived8443 a h
  have h4 : Entails.eval a c8448 := derived8448 a h
  have h5 : Entails.eval a c8449 := derived8449 a h
  have h6 : Entails.eval a c8450 := derived8450 a h
  have h7 : Entails.eval a c8229 := derived8229 a h
  have h8 : Entails.eval a c8453 := derived8453 a h
  have h9 : Entails.eval a c8230 := derived8230 a h
  have h10 : Entails.eval a c8461 := derived8461 a h
  have h11 : Entails.eval a c8462 := derived8462 a h
  have h12 : Entails.eval a c8463 := derived8463 a h
  have h13 : Entails.eval a c2180 := h 2179 (by decide)
  have h14 : Entails.eval a c2150 := h 2149 (by decide)
  have h15 : Entails.eval a c2160 := h 2159 (by decide)
  have h16 : Entails.eval a c2169 := h 2168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8465 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨31, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2180, some c2162, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8465 : lratChecker f8465 p8465 = .success := by decide +kernel
theorem unsat8465 : Unsatisfiable (PosFin 65) f8465 := by
  apply lratCheckerSound f8465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8465
  · intro a ha; simp [p8465] at ha; subst a; trivial
  · exact checked8465
theorem derived8465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8465 := by
  apply localUnsat_implies_entails f8465 [c2180, c2162] c8465 unsat8465 (by rfl) a
  have h0 : Entails.eval a c2180 := h 2179 (by decide)
  have h1 : Entails.eval a c2162 := h 2161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8466 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8443, some c8448, some c8460, some c8464, some c8457, some c7929, some c8458, some c8453, some c8459, some c8230, some c8152, some c8465, some c592, some c607, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8466 : lratChecker f8466 p8466 = .success := by decide +kernel
theorem unsat8466 : Unsatisfiable (PosFin 65) f8466 := by
  apply lratCheckerSound f8466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8466
  · intro a ha; simp [p8466] at ha; subst a; trivial
  · exact checked8466
theorem derived8466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8466 := by
  apply localUnsat_implies_entails f8466 [c8377, c7849, c8443, c8448, c8460, c8464, c8457, c7929, c8458, c8453, c8459, c8230, c8152, c8465, c592, c607] c8466 unsat8466 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8443 := derived8443 a h
  have h3 : Entails.eval a c8448 := derived8448 a h
  have h4 : Entails.eval a c8460 := derived8460 a h
  have h5 : Entails.eval a c8464 := derived8464 a h
  have h6 : Entails.eval a c8457 := derived8457 a h
  have h7 : Entails.eval a c7929 := derived7929 a h
  have h8 : Entails.eval a c8458 := derived8458 a h
  have h9 : Entails.eval a c8453 := derived8453 a h
  have h10 : Entails.eval a c8459 := derived8459 a h
  have h11 : Entails.eval a c8230 := derived8230 a h
  have h12 : Entails.eval a c8152 := derived8152 a h
  have h13 : Entails.eval a c8465 := derived8465 a h
  have h14 : Entails.eval a c592 := h 591 (by decide)
  have h15 : Entails.eval a c607 := h 606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8467 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8466, some c8377, some c7849, some c7765, some c8401, some c134, some c8402, some c1986, some c564, some c580, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8467 : lratChecker f8467 p8467 = .success := by decide +kernel
theorem unsat8467 : Unsatisfiable (PosFin 65) f8467 := by
  apply lratCheckerSound f8467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8467
  · intro a ha; simp [p8467] at ha; subst a; trivial
  · exact checked8467
theorem derived8467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8467 := by
  apply localUnsat_implies_entails f8467 [c8466, c8377, c7849, c7765, c8401, c134, c8402, c1986, c564, c580] c8467 unsat8467 (by rfl) a
  have h0 : Entails.eval a c8466 := derived8466 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c7765 := derived7765 a h
  have h4 : Entails.eval a c8401 := derived8401 a h
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c8402 := derived8402 a h
  have h7 : Entails.eval a c1986 := h 1985 (by decide)
  have h8 : Entails.eval a c564 := h 563 (by decide)
  have h9 : Entails.eval a c580 := h 579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8468 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8466, some c8377, some c7849, some c8380, some c8467, some c8395, some c8405, some c8189, some c1987, some c1999, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8468 : lratChecker f8468 p8468 = .success := by decide +kernel
theorem unsat8468 : Unsatisfiable (PosFin 65) f8468 := by
  apply lratCheckerSound f8468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8468
  · intro a ha; simp [p8468] at ha; subst a; trivial
  · exact checked8468
theorem derived8468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8468 := by
  apply localUnsat_implies_entails f8468 [c8466, c8377, c7849, c8380, c8467, c8395, c8405, c8189, c1987, c1999] c8468 unsat8468 (by rfl) a
  have h0 : Entails.eval a c8466 := derived8466 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8380 := derived8380 a h
  have h4 : Entails.eval a c8467 := derived8467 a h
  have h5 : Entails.eval a c8395 := derived8395 a h
  have h6 : Entails.eval a c8405 := derived8405 a h
  have h7 : Entails.eval a c8189 := derived8189 a h
  have h8 : Entails.eval a c1987 := h 1986 (by decide)
  have h9 : Entails.eval a c1999 := h 1998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8469 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7765, some c2990, some c2989, some c2986, some c2992, some c6733, some c2987, some c2985, some c6734, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8469 : lratChecker f8469 p8469 = .success := by decide +kernel
theorem unsat8469 : Unsatisfiable (PosFin 65) f8469 := by
  apply lratCheckerSound f8469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8469
  · intro a ha; simp [p8469] at ha; subst a; trivial
  · exact checked8469
theorem derived8469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8469 := by
  apply localUnsat_implies_entails f8469 [c7765, c2990, c2989, c2986, c2992, c6733, c2987, c2985, c6734] c8469 unsat8469 (by rfl) a
  have h0 : Entails.eval a c7765 := derived7765 a h
  have h1 : Entails.eval a c2990 := h 2989 (by decide)
  have h2 : Entails.eval a c2989 := h 2988 (by decide)
  have h3 : Entails.eval a c2986 := h 2985 (by decide)
  have h4 : Entails.eval a c2992 := h 2991 (by decide)
  have h5 : Entails.eval a c6733 := derived6733 a h
  have h6 : Entails.eval a c2987 := h 2986 (by decide)
  have h7 : Entails.eval a c2985 := h 2984 (by decide)
  have h8 : Entails.eval a c6734 := derived6734 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8470 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8468, some c8466, some c8469, some c7849, some c7961, some c8116, some c518, some c8236, some c8438, some c8379, some c2611, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8470 : lratChecker f8470 p8470 = .success := by decide +kernel
theorem unsat8470 : Unsatisfiable (PosFin 65) f8470 := by
  apply lratCheckerSound f8470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8470
  · intro a ha; simp [p8470] at ha; subst a; trivial
  · exact checked8470
theorem derived8470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8470 := by
  apply localUnsat_implies_entails f8470 [c8468, c8466, c8469, c7849, c7961, c8116, c518, c8236, c8438, c8379, c2611] c8470 unsat8470 (by rfl) a
  have h0 : Entails.eval a c8468 := derived8468 a h
  have h1 : Entails.eval a c8466 := derived8466 a h
  have h2 : Entails.eval a c8469 := derived8469 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c7961 := derived7961 a h
  have h5 : Entails.eval a c8116 := derived8116 a h
  have h6 : Entails.eval a c518 := h 517 (by decide)
  have h7 : Entails.eval a c8236 := derived8236 a h
  have h8 : Entails.eval a c8438 := derived8438 a h
  have h9 : Entails.eval a c8379 := derived8379 a h
  have h10 : Entails.eval a c2611 := h 2610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8471 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1291, some c1213, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8471 : lratChecker f8471 p8471 = .success := by decide +kernel
theorem unsat8471 : Unsatisfiable (PosFin 65) f8471 := by
  apply lratCheckerSound f8471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8471
  · intro a ha; simp [p8471] at ha; subst a; trivial
  · exact checked8471
theorem derived8471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8471 := by
  apply localUnsat_implies_entails f8471 [c1291, c1213] c8471 unsat8471 (by rfl) a
  have h0 : Entails.eval a c1291 := h 1290 (by decide)
  have h1 : Entails.eval a c1213 := h 1212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8472 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8470, some c8468, some c8466, some c8469, some c8377, some c7849, some c7929, some c8259, some c8112, some c7923, some c8020, some c7953, some c7958, some c8115, some c8471, some c8414, some c2577, some c572, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8472 : lratChecker f8472 p8472 = .success := by decide +kernel
theorem unsat8472 : Unsatisfiable (PosFin 65) f8472 := by
  apply lratCheckerSound f8472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8472
  · intro a ha; simp [p8472] at ha; subst a; trivial
  · exact checked8472
theorem derived8472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8472 := by
  apply localUnsat_implies_entails f8472 [c8470, c8468, c8466, c8469, c8377, c7849, c7929, c8259, c8112, c7923, c8020, c7953, c7958, c8115, c8471, c8414, c2577, c572] c8472 unsat8472 (by rfl) a
  have h0 : Entails.eval a c8470 := derived8470 a h
  have h1 : Entails.eval a c8468 := derived8468 a h
  have h2 : Entails.eval a c8466 := derived8466 a h
  have h3 : Entails.eval a c8469 := derived8469 a h
  have h4 : Entails.eval a c8377 := derived8377 a h
  have h5 : Entails.eval a c7849 := derived7849 a h
  have h6 : Entails.eval a c7929 := derived7929 a h
  have h7 : Entails.eval a c8259 := derived8259 a h
  have h8 : Entails.eval a c8112 := derived8112 a h
  have h9 : Entails.eval a c7923 := derived7923 a h
  have h10 : Entails.eval a c8020 := derived8020 a h
  have h11 : Entails.eval a c7953 := derived7953 a h
  have h12 : Entails.eval a c7958 := derived7958 a h
  have h13 : Entails.eval a c8115 := derived8115 a h
  have h14 : Entails.eval a c8471 := derived8471 a h
  have h15 : Entails.eval a c8414 := derived8414 a h
  have h16 : Entails.eval a c2577 := h 2576 (by decide)
  have h17 : Entails.eval a c572 := h 571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8473 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2142, some c2149, some c2162, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8473 : lratChecker f8473 p8473 = .success := by decide +kernel
theorem unsat8473 : Unsatisfiable (PosFin 65) f8473 := by
  apply lratCheckerSound f8473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8473
  · intro a ha; simp [p8473] at ha; subst a; trivial
  · exact checked8473
theorem derived8473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8473 := by
  apply localUnsat_implies_entails f8473 [c2142, c2149, c2162] c8473 unsat8473 (by rfl) a
  have h0 : Entails.eval a c2142 := h 2141 (by decide)
  have h1 : Entails.eval a c2149 := h 2148 (by decide)
  have h2 : Entails.eval a c2162 := h 2161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8474 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8466, some c8469, some c7849, some c8470, some c8472, some c8473, some c509, some c513, some c511, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8474 : lratChecker f8474 p8474 = .success := by decide +kernel
theorem unsat8474 : Unsatisfiable (PosFin 65) f8474 := by
  apply lratCheckerSound f8474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8474
  · intro a ha; simp [p8474] at ha; subst a; trivial
  · exact checked8474
theorem derived8474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8474 := by
  apply localUnsat_implies_entails f8474 [c8466, c8469, c7849, c8470, c8472, c8473, c509, c513, c511] c8474 unsat8474 (by rfl) a
  have h0 : Entails.eval a c8466 := derived8466 a h
  have h1 : Entails.eval a c8469 := derived8469 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8470 := derived8470 a h
  have h4 : Entails.eval a c8472 := derived8472 a h
  have h5 : Entails.eval a c8473 := derived8473 a h
  have h6 : Entails.eval a c509 := h 508 (by decide)
  have h7 : Entails.eval a c513 := h 512 (by decide)
  have h8 : Entails.eval a c511 := h 510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8475 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2319, some c2344, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8475 : lratChecker f8475 p8475 = .success := by decide +kernel
theorem unsat8475 : Unsatisfiable (PosFin 65) f8475 := by
  apply lratCheckerSound f8475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8475
  · intro a ha; simp [p8475] at ha; subst a; trivial
  · exact checked8475
theorem derived8475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8475 := by
  apply localUnsat_implies_entails f8475 [c2319, c2344] c8475 unsat8475 (by rfl) a
  have h0 : Entails.eval a c2319 := h 2318 (by decide)
  have h1 : Entails.eval a c2344 := h 2343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8476 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c676, some c675, some c8233, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8476 : lratChecker f8476 p8476 = .success := by decide +kernel
theorem unsat8476 : Unsatisfiable (PosFin 65) f8476 := by
  apply lratCheckerSound f8476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8476
  · intro a ha; simp [p8476] at ha; subst a; trivial
  · exact checked8476
theorem derived8476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8476 := by
  apply localUnsat_implies_entails f8476 [c676, c675, c8233] c8476 unsat8476 (by rfl) a
  have h0 : Entails.eval a c676 := h 675 (by decide)
  have h1 : Entails.eval a c675 := h 674 (by decide)
  have h2 : Entails.eval a c8233 := derived8233 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8477 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1918, some c606, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8477 : lratChecker f8477 p8477 = .success := by decide +kernel
theorem unsat8477 : Unsatisfiable (PosFin 65) f8477 := by
  apply lratCheckerSound f8477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8477
  · intro a ha; simp [p8477] at ha; subst a; trivial
  · exact checked8477
theorem derived8477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8477 := by
  apply localUnsat_implies_entails f8477 [c1918, c606] c8477 unsat8477 (by rfl) a
  have h0 : Entails.eval a c1918 := h 1917 (by decide)
  have h1 : Entails.eval a c606 := h 605 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8478 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c579, some c607, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8478 : lratChecker f8478 p8478 = .success := by decide +kernel
theorem unsat8478 : Unsatisfiable (PosFin 65) f8478 := by
  apply lratCheckerSound f8478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8478
  · intro a ha; simp [p8478] at ha; subst a; trivial
  · exact checked8478
theorem derived8478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8478 := by
  apply localUnsat_implies_entails f8478 [c579, c607] c8478 unsat8478 (by rfl) a
  have h0 : Entails.eval a c579 := h 578 (by decide)
  have h1 : Entails.eval a c607 := h 606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8479 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8466, some c8469, some c8474, some c8445, some c8249, some c8475, some c8346, some c8248, some c8476, some c8473, some c8477, some c8478, some c1987, some c1922, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8479 : lratChecker f8479 p8479 = .success := by decide +kernel
theorem unsat8479 : Unsatisfiable (PosFin 65) f8479 := by
  apply lratCheckerSound f8479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8479
  · intro a ha; simp [p8479] at ha; subst a; trivial
  · exact checked8479
theorem derived8479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8479 := by
  apply localUnsat_implies_entails f8479 [c8377, c7849, c8466, c8469, c8474, c8445, c8249, c8475, c8346, c8248, c8476, c8473, c8477, c8478, c1987, c1922] c8479 unsat8479 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8466 := derived8466 a h
  have h3 : Entails.eval a c8469 := derived8469 a h
  have h4 : Entails.eval a c8474 := derived8474 a h
  have h5 : Entails.eval a c8445 := derived8445 a h
  have h6 : Entails.eval a c8249 := derived8249 a h
  have h7 : Entails.eval a c8475 := derived8475 a h
  have h8 : Entails.eval a c8346 := derived8346 a h
  have h9 : Entails.eval a c8248 := derived8248 a h
  have h10 : Entails.eval a c8476 := derived8476 a h
  have h11 : Entails.eval a c8473 := derived8473 a h
  have h12 : Entails.eval a c8477 := derived8477 a h
  have h13 : Entails.eval a c8478 := derived8478 a h
  have h14 : Entails.eval a c1987 := h 1986 (by decide)
  have h15 : Entails.eval a c1922 := h 1921 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8480 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2131, some c969, some c1173, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p8480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8480 : lratChecker f8480 p8480 = .success := by decide +kernel
theorem unsat8480 : Unsatisfiable (PosFin 65) f8480 := by
  apply lratCheckerSound f8480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8480
  · intro a ha; simp [p8480] at ha; subst a; trivial
  · exact checked8480
theorem derived8480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8480 := by
  apply localUnsat_implies_entails f8480 [c2131, c969, c1173] c8480 unsat8480 (by rfl) a
  have h0 : Entails.eval a c2131 := h 2130 (by decide)
  have h1 : Entails.eval a c969 := h 968 (by decide)
  have h2 : Entails.eval a c1173 := h 1172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived8480

end CochromaticTwenty.Certificates.FixedCore1
