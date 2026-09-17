import MerLeanExperiment.Certificates.FixedCore1.Steps2600_2699

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8581 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8416, some c8420, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8581 : lratChecker f8581 p8581 = .success := by decide +kernel
theorem unsat8581 : Unsatisfiable (PosFin 65) f8581 := by
  apply lratCheckerSound f8581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8581
  · intro a ha; simp [p8581] at ha; subst a; trivial
  · exact checked8581
theorem derived8581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8581 := by
  apply localUnsat_implies_entails f8581 [c8416, c8420] c8581 unsat8581 (by rfl) a
  have h0 : Entails.eval a c8416 := derived8416 a h
  have h1 : Entails.eval a c8420 := derived8420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8582 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c492, some c564, some c1841, some c2549, some c1709, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8582 : lratChecker f8582 p8582 = .success := by decide +kernel
theorem unsat8582 : Unsatisfiable (PosFin 65) f8582 := by
  apply lratCheckerSound f8582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8582
  · intro a ha; simp [p8582] at ha; subst a; trivial
  · exact checked8582
theorem derived8582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8582 := by
  apply localUnsat_implies_entails f8582 [c492, c564, c1841, c2549, c1709] c8582 unsat8582 (by rfl) a
  have h0 : Entails.eval a c492 := h 491 (by decide)
  have h1 : Entails.eval a c564 := h 563 (by decide)
  have h2 : Entails.eval a c1841 := h 1840 (by decide)
  have h3 : Entails.eval a c2549 := h 2548 (by decide)
  have h4 : Entails.eval a c1709 := h 1708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8583 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2668, some c1885, some c1664, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8583 : lratChecker f8583 p8583 = .success := by decide +kernel
theorem unsat8583 : Unsatisfiable (PosFin 65) f8583 := by
  apply lratCheckerSound f8583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8583
  · intro a ha; simp [p8583] at ha; subst a; trivial
  · exact checked8583
theorem derived8583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8583 := by
  apply localUnsat_implies_entails f8583 [c2668, c1885, c1664] c8583 unsat8583 (by rfl) a
  have h0 : Entails.eval a c2668 := h 2667 (by decide)
  have h1 : Entails.eval a c1885 := h 1884 (by decide)
  have h2 : Entails.eval a c1664 := h 1663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8584 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8581, some c8383, some c8583, some c2488, some c8582, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8584 : lratChecker f8584 p8584 = .success := by decide +kernel
theorem unsat8584 : Unsatisfiable (PosFin 65) f8584 := by
  apply lratCheckerSound f8584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8584
  · intro a ha; simp [p8584] at ha; subst a; trivial
  · exact checked8584
theorem derived8584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8584 := by
  apply localUnsat_implies_entails f8584 [c8580, c8581, c8383, c8583, c2488, c8582] c8584 unsat8584 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8581 := derived8581 a h
  have h2 : Entails.eval a c8383 := derived8383 a h
  have h3 : Entails.eval a c8583 := derived8583 a h
  have h4 : Entails.eval a c2488 := h 2487 (by decide)
  have h5 : Entails.eval a c8582 := derived8582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8585 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8547, some c8580, some c89, some c1992, some c2111, some c560, some c1656, some c137, some c1396, some c3118, some c3113, some c1352, some c3115, some c87, some c6749, some c3101, some c93, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8585 : lratChecker f8585 p8585 = .success := by decide +kernel
theorem unsat8585 : Unsatisfiable (PosFin 65) f8585 := by
  apply lratCheckerSound f8585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8585
  · intro a ha; simp [p8585] at ha; subst a; trivial
  · exact checked8585
theorem derived8585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8585 := by
  apply localUnsat_implies_entails f8585 [c7849, c8377, c8547, c8580, c89, c1992, c2111, c560, c1656, c137, c1396, c3118, c3113, c1352, c3115, c87, c6749, c3101, c93] c8585 unsat8585 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c1992 := h 1991 (by decide)
  have h6 : Entails.eval a c2111 := h 2110 (by decide)
  have h7 : Entails.eval a c560 := h 559 (by decide)
  have h8 : Entails.eval a c1656 := h 1655 (by decide)
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c1396 := h 1395 (by decide)
  have h11 : Entails.eval a c3118 := h 3117 (by decide)
  have h12 : Entails.eval a c3113 := h 3112 (by decide)
  have h13 : Entails.eval a c1352 := h 1351 (by decide)
  have h14 : Entails.eval a c3115 := h 3114 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  have h16 : Entails.eval a c6749 := derived6749 a h
  have h17 : Entails.eval a c3101 := h 3100 (by decide)
  have h18 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8586 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8579, some c8547, some c8377, some c7849, some c8580, some c8584, some c8585, some c8578, some c8582, some c2124, some c580, some c1664, some c141, some c1270, some c3404, some c3403, some c3402, some c8079, some c1337, some c78, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8586 : lratChecker f8586 p8586 = .success := by decide +kernel
theorem unsat8586 : Unsatisfiable (PosFin 65) f8586 := by
  apply lratCheckerSound f8586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8586
  · intro a ha; simp [p8586] at ha; subst a; trivial
  · exact checked8586
theorem derived8586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8586 := by
  apply localUnsat_implies_entails f8586 [c8579, c8547, c8377, c7849, c8580, c8584, c8585, c8578, c8582, c2124, c580, c1664, c141, c1270, c3404, c3403, c3402, c8079, c1337, c78] c8586 unsat8586 (by rfl) a
  have h0 : Entails.eval a c8579 := derived8579 a h
  have h1 : Entails.eval a c8547 := derived8547 a h
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c8584 := derived8584 a h
  have h6 : Entails.eval a c8585 := derived8585 a h
  have h7 : Entails.eval a c8578 := derived8578 a h
  have h8 : Entails.eval a c8582 := derived8582 a h
  have h9 : Entails.eval a c2124 := h 2123 (by decide)
  have h10 : Entails.eval a c580 := h 579 (by decide)
  have h11 : Entails.eval a c1664 := h 1663 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c1270 := h 1269 (by decide)
  have h14 : Entails.eval a c3404 := h 3403 (by decide)
  have h15 : Entails.eval a c3403 := h 3402 (by decide)
  have h16 : Entails.eval a c3402 := h 3401 (by decide)
  have h17 : Entails.eval a c8079 := derived8079 a h
  have h18 : Entails.eval a c1337 := h 1336 (by decide)
  have h19 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8587 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6707, some c6705, some c6706, some c2266, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p8587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8587 : lratChecker f8587 p8587 = .success := by decide +kernel
theorem unsat8587 : Unsatisfiable (PosFin 65) f8587 := by
  apply lratCheckerSound f8587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8587
  · intro a ha; simp [p8587] at ha; subst a; trivial
  · exact checked8587
theorem derived8587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8587 := by
  apply localUnsat_implies_entails f8587 [c6707, c6705, c6706, c2266] c8587 unsat8587 (by rfl) a
  have h0 : Entails.eval a c6707 := derived6707 a h
  have h1 : Entails.eval a c6705 := derived6705 a h
  have h2 : Entails.eval a c6706 := derived6706 a h
  have h3 : Entails.eval a c2266 := h 2265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8588 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8586, some c8579, some c8451, some c8383, some c8547, some c2379, some c2371, some c2394, some c2375, some c8566, some c2377, some c673, some c588, some c2363, some c2558, some c7846, some c1710, some c8565, some c8587, some c167, some c1863, some c1864, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked8588 : lratChecker f8588 p8588 = .success := by decide +kernel
theorem unsat8588 : Unsatisfiable (PosFin 65) f8588 := by
  apply lratCheckerSound f8588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8588
  · intro a ha; simp [p8588] at ha; subst a; trivial
  · exact checked8588
theorem derived8588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8588 := by
  apply localUnsat_implies_entails f8588 [c7849, c8377, c8586, c8579, c8451, c8383, c8547, c2379, c2371, c2394, c2375, c8566, c2377, c673, c588, c2363, c2558, c7846, c1710, c8565, c8587, c167, c1863, c1864] c8588 unsat8588 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8586 := derived8586 a h
  have h3 : Entails.eval a c8579 := derived8579 a h
  have h4 : Entails.eval a c8451 := derived8451 a h
  have h5 : Entails.eval a c8383 := derived8383 a h
  have h6 : Entails.eval a c8547 := derived8547 a h
  have h7 : Entails.eval a c2379 := h 2378 (by decide)
  have h8 : Entails.eval a c2371 := h 2370 (by decide)
  have h9 : Entails.eval a c2394 := h 2393 (by decide)
  have h10 : Entails.eval a c2375 := h 2374 (by decide)
  have h11 : Entails.eval a c8566 := derived8566 a h
  have h12 : Entails.eval a c2377 := h 2376 (by decide)
  have h13 : Entails.eval a c673 := h 672 (by decide)
  have h14 : Entails.eval a c588 := h 587 (by decide)
  have h15 : Entails.eval a c2363 := h 2362 (by decide)
  have h16 : Entails.eval a c2558 := h 2557 (by decide)
  have h17 : Entails.eval a c7846 := derived7846 a h
  have h18 : Entails.eval a c1710 := h 1709 (by decide)
  have h19 : Entails.eval a c8565 := derived8565 a h
  have h20 : Entails.eval a c8587 := derived8587 a h
  have h21 : Entails.eval a c167 := h 166 (by decide)
  have h22 : Entails.eval a c1863 := h 1862 (by decide)
  have h23 : Entails.eval a c1864 := h 1863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8589 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8586, some c8579, some c8451, some c8547, some c8383, some c2394, some c2379, some c2377, some c8566, some c2375, some c2371, some c2397, some c8509, some c2388, some c8588, some c690, some c2365, some c608, some c2604, some c2558, some c1294, some c1626, some c8565, some c8587, some c3351, some c1240, some c2367, some c72, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked8589 : lratChecker f8589 p8589 = .success := by decide +kernel
theorem unsat8589 : Unsatisfiable (PosFin 65) f8589 := by
  apply lratCheckerSound f8589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8589
  · intro a ha; simp [p8589] at ha; subst a; trivial
  · exact checked8589
theorem derived8589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8589 := by
  apply localUnsat_implies_entails f8589 [c7849, c8377, c8586, c8579, c8451, c8547, c8383, c2394, c2379, c2377, c8566, c2375, c2371, c2397, c8509, c2388, c8588, c690, c2365, c608, c2604, c2558, c1294, c1626, c8565, c8587, c3351, c1240, c2367, c72] c8589 unsat8589 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8586 := derived8586 a h
  have h3 : Entails.eval a c8579 := derived8579 a h
  have h4 : Entails.eval a c8451 := derived8451 a h
  have h5 : Entails.eval a c8547 := derived8547 a h
  have h6 : Entails.eval a c8383 := derived8383 a h
  have h7 : Entails.eval a c2394 := h 2393 (by decide)
  have h8 : Entails.eval a c2379 := h 2378 (by decide)
  have h9 : Entails.eval a c2377 := h 2376 (by decide)
  have h10 : Entails.eval a c8566 := derived8566 a h
  have h11 : Entails.eval a c2375 := h 2374 (by decide)
  have h12 : Entails.eval a c2371 := h 2370 (by decide)
  have h13 : Entails.eval a c2397 := h 2396 (by decide)
  have h14 : Entails.eval a c8509 := derived8509 a h
  have h15 : Entails.eval a c2388 := h 2387 (by decide)
  have h16 : Entails.eval a c8588 := derived8588 a h
  have h17 : Entails.eval a c690 := h 689 (by decide)
  have h18 : Entails.eval a c2365 := h 2364 (by decide)
  have h19 : Entails.eval a c608 := h 607 (by decide)
  have h20 : Entails.eval a c2604 := h 2603 (by decide)
  have h21 : Entails.eval a c2558 := h 2557 (by decide)
  have h22 : Entails.eval a c1294 := h 1293 (by decide)
  have h23 : Entails.eval a c1626 := h 1625 (by decide)
  have h24 : Entails.eval a c8565 := derived8565 a h
  have h25 : Entails.eval a c8587 := derived8587 a h
  have h26 : Entails.eval a c3351 := h 3350 (by decide)
  have h27 : Entails.eval a c1240 := h 1239 (by decide)
  have h28 : Entails.eval a c2367 := h 2366 (by decide)
  have h29 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8590 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8586, some c8579, some c8547, some c8377, some c7849, some c8451, some c8589, some c8455, some c1942, some c673, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8590 : lratChecker f8590 p8590 = .success := by decide +kernel
theorem unsat8590 : Unsatisfiable (PosFin 65) f8590 := by
  apply lratCheckerSound f8590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8590
  · intro a ha; simp [p8590] at ha; subst a; trivial
  · exact checked8590
theorem derived8590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8590 := by
  apply localUnsat_implies_entails f8590 [c8586, c8579, c8547, c8377, c7849, c8451, c8589, c8455, c1942, c673] c8590 unsat8590 (by rfl) a
  have h0 : Entails.eval a c8586 := derived8586 a h
  have h1 : Entails.eval a c8579 := derived8579 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8377 := derived8377 a h
  have h4 : Entails.eval a c7849 := derived7849 a h
  have h5 : Entails.eval a c8451 := derived8451 a h
  have h6 : Entails.eval a c8589 := derived8589 a h
  have h7 : Entails.eval a c8455 := derived8455 a h
  have h8 : Entails.eval a c1942 := h 1941 (by decide)
  have h9 : Entails.eval a c673 := h 672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8591 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8581, some c1900, some c8462, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8591 : lratChecker f8591 p8591 = .success := by decide +kernel
theorem unsat8591 : Unsatisfiable (PosFin 65) f8591 := by
  apply lratCheckerSound f8591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8591
  · intro a ha; simp [p8591] at ha; subst a; trivial
  · exact checked8591
theorem derived8591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8591 := by
  apply localUnsat_implies_entails f8591 [c8581, c1900, c8462] c8591 unsat8591 (by rfl) a
  have h0 : Entails.eval a c8581 := derived8581 a h
  have h1 : Entails.eval a c1900 := h 1899 (by decide)
  have h2 : Entails.eval a c8462 := derived8462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8592 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8591, some c8383, some c2394, some c2379, some c2377, some c8566, some c2375, some c8552, some c7300, some c7299, some c2294, some c2312, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8592 : lratChecker f8592 p8592 = .success := by decide +kernel
theorem unsat8592 : Unsatisfiable (PosFin 65) f8592 := by
  apply lratCheckerSound f8592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8592
  · intro a ha; simp [p8592] at ha; subst a; trivial
  · exact checked8592
theorem derived8592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8592 := by
  apply localUnsat_implies_entails f8592 [c8591, c8383, c2394, c2379, c2377, c8566, c2375, c8552, c7300, c7299, c2294, c2312] c8592 unsat8592 (by rfl) a
  have h0 : Entails.eval a c8591 := derived8591 a h
  have h1 : Entails.eval a c8383 := derived8383 a h
  have h2 : Entails.eval a c2394 := h 2393 (by decide)
  have h3 : Entails.eval a c2379 := h 2378 (by decide)
  have h4 : Entails.eval a c2377 := h 2376 (by decide)
  have h5 : Entails.eval a c8566 := derived8566 a h
  have h6 : Entails.eval a c2375 := h 2374 (by decide)
  have h7 : Entails.eval a c8552 := derived8552 a h
  have h8 : Entails.eval a c7300 := derived7300 a h
  have h9 : Entails.eval a c7299 := derived7299 a h
  have h10 : Entails.eval a c2294 := h 2293 (by decide)
  have h11 : Entails.eval a c2312 := h 2311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8593 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8578, some c2157, some c588, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8593 : lratChecker f8593 p8593 = .success := by decide +kernel
theorem unsat8593 : Unsatisfiable (PosFin 65) f8593 := by
  apply lratCheckerSound f8593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8593
  · intro a ha; simp [p8593] at ha; subst a; trivial
  · exact checked8593
theorem derived8593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8593 := by
  apply localUnsat_implies_entails f8593 [c8578, c2157, c588] c8593 unsat8593 (by rfl) a
  have h0 : Entails.eval a c8578 := derived8578 a h
  have h1 : Entails.eval a c2157 := h 2156 (by decide)
  have h2 : Entails.eval a c588 := h 587 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8594 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8579, some c8547, some c8377, some c7849, some c8586, some c8590, some c8591, some c8592, some c8578, some c8593, some c580, some c1956, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8594 : lratChecker f8594 p8594 = .success := by decide +kernel
theorem unsat8594 : Unsatisfiable (PosFin 65) f8594 := by
  apply lratCheckerSound f8594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8594
  · intro a ha; simp [p8594] at ha; subst a; trivial
  · exact checked8594
theorem derived8594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8594 := by
  apply localUnsat_implies_entails f8594 [c8579, c8547, c8377, c7849, c8586, c8590, c8591, c8592, c8578, c8593, c580, c1956] c8594 unsat8594 (by rfl) a
  have h0 : Entails.eval a c8579 := derived8579 a h
  have h1 : Entails.eval a c8547 := derived8547 a h
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8586 := derived8586 a h
  have h5 : Entails.eval a c8590 := derived8590 a h
  have h6 : Entails.eval a c8591 := derived8591 a h
  have h7 : Entails.eval a c8592 := derived8592 a h
  have h8 : Entails.eval a c8578 := derived8578 a h
  have h9 : Entails.eval a c8593 := derived8593 a h
  have h10 : Entails.eval a c580 := h 579 (by decide)
  have h11 : Entails.eval a c1956 := h 1955 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8595 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8575, some c525, some c538, some c550, some c536, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8595 : lratChecker f8595 p8595 = .success := by decide +kernel
theorem unsat8595 : Unsatisfiable (PosFin 65) f8595 := by
  apply lratCheckerSound f8595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8595
  · intro a ha; simp [p8595] at ha; subst a; trivial
  · exact checked8595
theorem derived8595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8595 := by
  apply localUnsat_implies_entails f8595 [c8575, c525, c538, c550, c536] c8595 unsat8595 (by rfl) a
  have h0 : Entails.eval a c8575 := derived8575 a h
  have h1 : Entails.eval a c525 := h 524 (by decide)
  have h2 : Entails.eval a c538 := h 537 (by decide)
  have h3 : Entails.eval a c550 := h 549 (by decide)
  have h4 : Entails.eval a c536 := h 535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8596 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c579, some c563, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8596 : lratChecker f8596 p8596 = .success := by decide +kernel
theorem unsat8596 : Unsatisfiable (PosFin 65) f8596 := by
  apply lratCheckerSound f8596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8596
  · intro a ha; simp [p8596] at ha; subst a; trivial
  · exact checked8596
theorem derived8596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8596 := by
  apply localUnsat_implies_entails f8596 [c579, c563] c8596 unsat8596 (by rfl) a
  have h0 : Entails.eval a c579 := h 578 (by decide)
  have h1 : Entails.eval a c563 := h 562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8597 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c509, some c8434, some c2577, some c2556, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8597 : lratChecker f8597 p8597 = .success := by decide +kernel
theorem unsat8597 : Unsatisfiable (PosFin 65) f8597 := by
  apply lratCheckerSound f8597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8597
  · intro a ha; simp [p8597] at ha; subst a; trivial
  · exact checked8597
theorem derived8597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8597 := by
  apply localUnsat_implies_entails f8597 [c509, c8434, c2577, c2556] c8597 unsat8597 (by rfl) a
  have h0 : Entails.eval a c509 := h 508 (by decide)
  have h1 : Entails.eval a c8434 := derived8434 a h
  have h2 : Entails.eval a c2577 := h 2576 (by decide)
  have h3 : Entails.eval a c2556 := h 2555 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8598 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c513, some c602, some c600, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8598 : lratChecker f8598 p8598 = .success := by decide +kernel
theorem unsat8598 : Unsatisfiable (PosFin 65) f8598 := by
  apply lratCheckerSound f8598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8598
  · intro a ha; simp [p8598] at ha; subst a; trivial
  · exact checked8598
theorem derived8598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8598 := by
  apply localUnsat_implies_entails f8598 [c513, c602, c600] c8598 unsat8598 (by rfl) a
  have h0 : Entails.eval a c513 := h 512 (by decide)
  have h1 : Entails.eval a c602 := h 601 (by decide)
  have h2 : Entails.eval a c600 := h 599 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8599 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8596, some c8597, some c8598, some c2577, some c1479, some c2592, some c1312, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8599 : lratChecker f8599 p8599 = .success := by decide +kernel
theorem unsat8599 : Unsatisfiable (PosFin 65) f8599 := by
  apply lratCheckerSound f8599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8599
  · intro a ha; simp [p8599] at ha; subst a; trivial
  · exact checked8599
theorem derived8599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8599 := by
  apply localUnsat_implies_entails f8599 [c8596, c8597, c8598, c2577, c1479, c2592, c1312] c8599 unsat8599 (by rfl) a
  have h0 : Entails.eval a c8596 := derived8596 a h
  have h1 : Entails.eval a c8597 := derived8597 a h
  have h2 : Entails.eval a c8598 := derived8598 a h
  have h3 : Entails.eval a c2577 := h 2576 (by decide)
  have h4 : Entails.eval a c1479 := h 1478 (by decide)
  have h5 : Entails.eval a c2592 := h 2591 (by decide)
  have h6 : Entails.eval a c1312 := h 1311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8600 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2099, some c1602, some c1861, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8600 : lratChecker f8600 p8600 = .success := by decide +kernel
theorem unsat8600 : Unsatisfiable (PosFin 65) f8600 := by
  apply lratCheckerSound f8600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8600
  · intro a ha; simp [p8600] at ha; subst a; trivial
  · exact checked8600
theorem derived8600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8600 := by
  apply localUnsat_implies_entails f8600 [c2099, c1602, c1861] c8600 unsat8600 (by rfl) a
  have h0 : Entails.eval a c2099 := h 2098 (by decide)
  have h1 : Entails.eval a c1602 := h 1601 (by decide)
  have h2 : Entails.eval a c1861 := h 1860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8601 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8596, some c8599, some c8600, some c8598, some c2577, some c2100, some c1883, some c1603, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8601 : lratChecker f8601 p8601 = .success := by decide +kernel
theorem unsat8601 : Unsatisfiable (PosFin 65) f8601 := by
  apply lratCheckerSound f8601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8601
  · intro a ha; simp [p8601] at ha; subst a; trivial
  · exact checked8601
theorem derived8601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8601 := by
  apply localUnsat_implies_entails f8601 [c8596, c8599, c8600, c8598, c2577, c2100, c1883, c1603] c8601 unsat8601 (by rfl) a
  have h0 : Entails.eval a c8596 := derived8596 a h
  have h1 : Entails.eval a c8599 := derived8599 a h
  have h2 : Entails.eval a c8600 := derived8600 a h
  have h3 : Entails.eval a c8598 := derived8598 a h
  have h4 : Entails.eval a c2577 := h 2576 (by decide)
  have h5 : Entails.eval a c2100 := h 2099 (by decide)
  have h6 : Entails.eval a c1883 := h 1882 (by decide)
  have h7 : Entails.eval a c1603 := h 1602 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8602 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2433, some c2428, some c482, some c2491, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8602 : lratChecker f8602 p8602 = .success := by decide +kernel
theorem unsat8602 : Unsatisfiable (PosFin 65) f8602 := by
  apply lratCheckerSound f8602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8602
  · intro a ha; simp [p8602] at ha; subst a; trivial
  · exact checked8602
theorem derived8602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8602 := by
  apply localUnsat_implies_entails f8602 [c2433, c2428, c482, c2491] c8602 unsat8602 (by rfl) a
  have h0 : Entails.eval a c2433 := h 2432 (by decide)
  have h1 : Entails.eval a c2428 := h 2427 (by decide)
  have h2 : Entails.eval a c482 := h 481 (by decide)
  have h3 : Entails.eval a c2491 := h 2490 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8603 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2100, some c2498, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8603 : lratChecker f8603 p8603 = .success := by decide +kernel
theorem unsat8603 : Unsatisfiable (PosFin 65) f8603 := by
  apply lratCheckerSound f8603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8603
  · intro a ha; simp [p8603] at ha; subst a; trivial
  · exact checked8603
theorem derived8603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8603 := by
  apply localUnsat_implies_entails f8603 [c2100, c2498] c8603 unsat8603 (by rfl) a
  have h0 : Entails.eval a c2100 := h 2099 (by decide)
  have h1 : Entails.eval a c2498 := h 2497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8604 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8601, some c8602, some c8600, some c8603, some c482, some c8432, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8604 : lratChecker f8604 p8604 = .success := by decide +kernel
theorem unsat8604 : Unsatisfiable (PosFin 65) f8604 := by
  apply lratCheckerSound f8604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8604
  · intro a ha; simp [p8604] at ha; subst a; trivial
  · exact checked8604
theorem derived8604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8604 := by
  apply localUnsat_implies_entails f8604 [c8601, c8602, c8600, c8603, c482, c8432] c8604 unsat8604 (by rfl) a
  have h0 : Entails.eval a c8601 := derived8601 a h
  have h1 : Entails.eval a c8602 := derived8602 a h
  have h2 : Entails.eval a c8600 := derived8600 a h
  have h3 : Entails.eval a c8603 := derived8603 a h
  have h4 : Entails.eval a c482 := h 481 (by decide)
  have h5 : Entails.eval a c8432 := derived8432 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8605 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c509, some c2178, some c8354, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8605 : lratChecker f8605 p8605 = .success := by decide +kernel
theorem unsat8605 : Unsatisfiable (PosFin 65) f8605 := by
  apply lratCheckerSound f8605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8605
  · intro a ha; simp [p8605] at ha; subst a; trivial
  · exact checked8605
theorem derived8605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8605 := by
  apply localUnsat_implies_entails f8605 [c509, c2178, c8354] c8605 unsat8605 (by rfl) a
  have h0 : Entails.eval a c509 := h 508 (by decide)
  have h1 : Entails.eval a c2178 := h 2177 (by decide)
  have h2 : Entails.eval a c8354 := derived8354 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8606 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8595, some c8604, some c8577, some c8596, some c8605, some c8598, some c2577, some c2052, some c2170, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8606 : lratChecker f8606 p8606 = .success := by decide +kernel
theorem unsat8606 : Unsatisfiable (PosFin 65) f8606 := by
  apply lratCheckerSound f8606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8606
  · intro a ha; simp [p8606] at ha; subst a; trivial
  · exact checked8606
theorem derived8606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8606 := by
  apply localUnsat_implies_entails f8606 [c8595, c8604, c8577, c8596, c8605, c8598, c2577, c2052, c2170] c8606 unsat8606 (by rfl) a
  have h0 : Entails.eval a c8595 := derived8595 a h
  have h1 : Entails.eval a c8604 := derived8604 a h
  have h2 : Entails.eval a c8577 := derived8577 a h
  have h3 : Entails.eval a c8596 := derived8596 a h
  have h4 : Entails.eval a c8605 := derived8605 a h
  have h5 : Entails.eval a c8598 := derived8598 a h
  have h6 : Entails.eval a c2577 := h 2576 (by decide)
  have h7 : Entails.eval a c2052 := h 2051 (by decide)
  have h8 : Entails.eval a c2170 := h 2169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8607 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c457, some c509, some c1854, some c2612, some c1638, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8607 : lratChecker f8607 p8607 = .success := by decide +kernel
theorem unsat8607 : Unsatisfiable (PosFin 65) f8607 := by
  apply lratCheckerSound f8607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8607
  · intro a ha; simp [p8607] at ha; subst a; trivial
  · exact checked8607
theorem derived8607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8607 := by
  apply localUnsat_implies_entails f8607 [c457, c509, c1854, c2612, c1638] c8607 unsat8607 (by rfl) a
  have h0 : Entails.eval a c457 := h 456 (by decide)
  have h1 : Entails.eval a c509 := h 508 (by decide)
  have h2 : Entails.eval a c1854 := h 1853 (by decide)
  have h3 : Entails.eval a c2612 := h 2611 (by decide)
  have h4 : Entails.eval a c1638 := h 1637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8608 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8582, some c481, some c2667, some c1884, some c1660, some c1683, some c1689, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8608 : lratChecker f8608 p8608 = .success := by decide +kernel
theorem unsat8608 : Unsatisfiable (PosFin 65) f8608 := by
  apply lratCheckerSound f8608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8608
  · intro a ha; simp [p8608] at ha; subst a; trivial
  · exact checked8608
theorem derived8608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8608 := by
  apply localUnsat_implies_entails f8608 [c8582, c481, c2667, c1884, c1660, c1683, c1689] c8608 unsat8608 (by rfl) a
  have h0 : Entails.eval a c8582 := derived8582 a h
  have h1 : Entails.eval a c481 := h 480 (by decide)
  have h2 : Entails.eval a c2667 := h 2666 (by decide)
  have h3 : Entails.eval a c1884 := h 1883 (by decide)
  have h4 : Entails.eval a c1660 := h 1659 (by decide)
  have h5 : Entails.eval a c1683 := h 1682 (by decide)
  have h6 : Entails.eval a c1689 := h 1688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8609 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2432, some c2430, some c2445, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8609 : lratChecker f8609 p8609 = .success := by decide +kernel
theorem unsat8609 : Unsatisfiable (PosFin 65) f8609 := by
  apply lratCheckerSound f8609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8609
  · intro a ha; simp [p8609] at ha; subst a; trivial
  · exact checked8609
theorem derived8609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8609 := by
  apply localUnsat_implies_entails f8609 [c2432, c2430, c2445] c8609 unsat8609 (by rfl) a
  have h0 : Entails.eval a c2432 := h 2431 (by decide)
  have h1 : Entails.eval a c2430 := h 2429 (by decide)
  have h2 : Entails.eval a c2445 := h 2444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8610 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8606, some c8595, some c8607, some c8608, some c8609, some c8603, some c482, some c8432, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8610 : lratChecker f8610 p8610 = .success := by decide +kernel
theorem unsat8610 : Unsatisfiable (PosFin 65) f8610 := by
  apply lratCheckerSound f8610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8610
  · intro a ha; simp [p8610] at ha; subst a; trivial
  · exact checked8610
theorem derived8610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8610 := by
  apply localUnsat_implies_entails f8610 [c8606, c8595, c8607, c8608, c8609, c8603, c482, c8432] c8610 unsat8610 (by rfl) a
  have h0 : Entails.eval a c8606 := derived8606 a h
  have h1 : Entails.eval a c8595 := derived8595 a h
  have h2 : Entails.eval a c8607 := derived8607 a h
  have h3 : Entails.eval a c8608 := derived8608 a h
  have h4 : Entails.eval a c8609 := derived8609 a h
  have h5 : Entails.eval a c8603 := derived8603 a h
  have h6 : Entails.eval a c482 := h 481 (by decide)
  have h7 : Entails.eval a c8432 := derived8432 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8611 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8595, some c8606, some c8610, some c8578, some c8593, some c8605, some c8598, some c2152, some c2156, some c2173, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8611 : lratChecker f8611 p8611 = .success := by decide +kernel
theorem unsat8611 : Unsatisfiable (PosFin 65) f8611 := by
  apply lratCheckerSound f8611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8611
  · intro a ha; simp [p8611] at ha; subst a; trivial
  · exact checked8611
theorem derived8611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8611 := by
  apply localUnsat_implies_entails f8611 [c8595, c8606, c8610, c8578, c8593, c8605, c8598, c2152, c2156, c2173] c8611 unsat8611 (by rfl) a
  have h0 : Entails.eval a c8595 := derived8595 a h
  have h1 : Entails.eval a c8606 := derived8606 a h
  have h2 : Entails.eval a c8610 := derived8610 a h
  have h3 : Entails.eval a c8578 := derived8578 a h
  have h4 : Entails.eval a c8593 := derived8593 a h
  have h5 : Entails.eval a c8605 := derived8605 a h
  have h6 : Entails.eval a c8598 := derived8598 a h
  have h7 : Entails.eval a c2152 := h 2151 (by decide)
  have h8 : Entails.eval a c2156 := h 2155 (by decide)
  have h9 : Entails.eval a c2173 := h 2172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8612 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2251, some c2262, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8612 : lratChecker f8612 p8612 = .success := by decide +kernel
theorem unsat8612 : Unsatisfiable (PosFin 65) f8612 := by
  apply lratCheckerSound f8612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8612
  · intro a ha; simp [p8612] at ha; subst a; trivial
  · exact checked8612
theorem derived8612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8612 := by
  apply localUnsat_implies_entails f8612 [c2251, c2262] c8612 unsat8612 (by rfl) a
  have h0 : Entails.eval a c2251 := h 2250 (by decide)
  have h1 : Entails.eval a c2262 := h 2261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8613 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2403, some c482, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8613 : lratChecker f8613 p8613 = .success := by decide +kernel
theorem unsat8613 : Unsatisfiable (PosFin 65) f8613 := by
  apply lratCheckerSound f8613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8613
  · intro a ha; simp [p8613] at ha; subst a; trivial
  · exact checked8613
theorem derived8613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8613 := by
  apply localUnsat_implies_entails f8613 [c2403, c482] c8613 unsat8613 (by rfl) a
  have h0 : Entails.eval a c2403 := h 2402 (by decide)
  have h1 : Entails.eval a c482 := h 481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8614 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8612, some c8596, some c8613, some c2194, some c2218, some c2089, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8614 : lratChecker f8614 p8614 = .success := by decide +kernel
theorem unsat8614 : Unsatisfiable (PosFin 65) f8614 := by
  apply lratCheckerSound f8614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8614
  · intro a ha; simp [p8614] at ha; subst a; trivial
  · exact checked8614
theorem derived8614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8614 := by
  apply localUnsat_implies_entails f8614 [c8612, c8596, c8613, c2194, c2218, c2089] c8614 unsat8614 (by rfl) a
  have h0 : Entails.eval a c8612 := derived8612 a h
  have h1 : Entails.eval a c8596 := derived8596 a h
  have h2 : Entails.eval a c8613 := derived8613 a h
  have h3 : Entails.eval a c2194 := h 2193 (by decide)
  have h4 : Entails.eval a c2218 := h 2217 (by decide)
  have h5 : Entails.eval a c2089 := h 2088 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8615 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8612, some c8596, some c8614, some c1922, some c1903, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8615 : lratChecker f8615 p8615 = .success := by decide +kernel
theorem unsat8615 : Unsatisfiable (PosFin 65) f8615 := by
  apply lratCheckerSound f8615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8615
  · intro a ha; simp [p8615] at ha; subst a; trivial
  · exact checked8615
theorem derived8615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8615 := by
  apply localUnsat_implies_entails f8615 [c8612, c8596, c8614, c1922, c1903] c8615 unsat8615 (by rfl) a
  have h0 : Entails.eval a c8612 := derived8612 a h
  have h1 : Entails.eval a c8596 := derived8596 a h
  have h2 : Entails.eval a c8614 := derived8614 a h
  have h3 : Entails.eval a c1922 := h 1921 (by decide)
  have h4 : Entails.eval a c1903 := h 1902 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8616 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c457, some c2400, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8616 : lratChecker f8616 p8616 = .success := by decide +kernel
theorem unsat8616 : Unsatisfiable (PosFin 65) f8616 := by
  apply lratCheckerSound f8616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8616
  · intro a ha; simp [p8616] at ha; subst a; trivial
  · exact checked8616
theorem derived8616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8616 := by
  apply localUnsat_implies_entails f8616 [c457, c2400] c8616 unsat8616 (by rfl) a
  have h0 : Entails.eval a c457 := h 456 (by decide)
  have h1 : Entails.eval a c2400 := h 2399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8617 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8615, some c8613, some c8616, some c2343, some c2100, some c2402, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8617 : lratChecker f8617 p8617 = .success := by decide +kernel
theorem unsat8617 : Unsatisfiable (PosFin 65) f8617 := by
  apply lratCheckerSound f8617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8617
  · intro a ha; simp [p8617] at ha; subst a; trivial
  · exact checked8617
theorem derived8617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8617 := by
  apply localUnsat_implies_entails f8617 [c8615, c8613, c8616, c2343, c2100, c2402] c8617 unsat8617 (by rfl) a
  have h0 : Entails.eval a c8615 := derived8615 a h
  have h1 : Entails.eval a c8613 := derived8613 a h
  have h2 : Entails.eval a c8616 := derived8616 a h
  have h3 : Entails.eval a c2343 := h 2342 (by decide)
  have h4 : Entails.eval a c2100 := h 2099 (by decide)
  have h5 : Entails.eval a c2402 := h 2401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8618 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c124, some c8477, some c156, some c3090, some c3093, some c3386, some c3088, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8618 : lratChecker f8618 p8618 = .success := by decide +kernel
theorem unsat8618 : Unsatisfiable (PosFin 65) f8618 := by
  apply lratCheckerSound f8618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8618
  · intro a ha; simp [p8618] at ha; subst a; trivial
  · exact checked8618
theorem derived8618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8618 := by
  apply localUnsat_implies_entails f8618 [c124, c8477, c156, c3090, c3093, c3386, c3088] c8618 unsat8618 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c8477 := derived8477 a h
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c3090 := h 3089 (by decide)
  have h4 : Entails.eval a c3093 := h 3092 (by decide)
  have h5 : Entails.eval a c3386 := h 3385 (by decide)
  have h6 : Entails.eval a c3088 := h 3087 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8619 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6771, some c6772, some c6773, some c3393, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p8619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8619 : lratChecker f8619 p8619 = .success := by decide +kernel
theorem unsat8619 : Unsatisfiable (PosFin 65) f8619 := by
  apply lratCheckerSound f8619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8619
  · intro a ha; simp [p8619] at ha; subst a; trivial
  · exact checked8619
theorem derived8619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8619 := by
  apply localUnsat_implies_entails f8619 [c6771, c6772, c6773, c3393] c8619 unsat8619 (by rfl) a
  have h0 : Entails.eval a c6771 := derived6771 a h
  have h1 : Entails.eval a c6772 := derived6772 a h
  have h2 : Entails.eval a c6773 := derived6773 a h
  have h3 : Entails.eval a c3393 := h 3392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8620 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c125, some c8619, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p8620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8620 : lratChecker f8620 p8620 = .success := by decide +kernel
theorem unsat8620 : Unsatisfiable (PosFin 65) f8620 := by
  apply lratCheckerSound f8620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8620
  · intro a ha; simp [p8620] at ha; subst a; trivial
  · exact checked8620
theorem derived8620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8620 := by
  apply localUnsat_implies_entails f8620 [c125, c8619] c8620 unsat8620 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c8619 := derived8619 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8621 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8547, some c8377, some c7849, some c8579, some c8594, some c8611, some c8615, some c8617, some c8618, some c8620, some c2262, some c579, some c1921, some c1927, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8621 : lratChecker f8621 p8621 = .success := by decide +kernel
theorem unsat8621 : Unsatisfiable (PosFin 65) f8621 := by
  apply lratCheckerSound f8621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8621
  · intro a ha; simp [p8621] at ha; subst a; trivial
  · exact checked8621
theorem derived8621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8621 := by
  apply localUnsat_implies_entails f8621 [c8547, c8377, c7849, c8579, c8594, c8611, c8615, c8617, c8618, c8620, c2262, c579, c1921, c1927] c8621 unsat8621 (by rfl) a
  have h0 : Entails.eval a c8547 := derived8547 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8579 := derived8579 a h
  have h4 : Entails.eval a c8594 := derived8594 a h
  have h5 : Entails.eval a c8611 := derived8611 a h
  have h6 : Entails.eval a c8615 := derived8615 a h
  have h7 : Entails.eval a c8617 := derived8617 a h
  have h8 : Entails.eval a c8618 := derived8618 a h
  have h9 : Entails.eval a c8620 := derived8620 a h
  have h10 : Entails.eval a c2262 := h 2261 (by decide)
  have h11 : Entails.eval a c579 := h 578 (by decide)
  have h12 : Entails.eval a c1921 := h 1920 (by decide)
  have h13 : Entails.eval a c1927 := h 1926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8622 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8547, some c8377, some c7849, some c8580, some c8581, some c8585, some c8402, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8622 : lratChecker f8622 p8622 = .success := by decide +kernel
theorem unsat8622 : Unsatisfiable (PosFin 65) f8622 := by
  apply lratCheckerSound f8622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8622
  · intro a ha; simp [p8622] at ha; subst a; trivial
  · exact checked8622
theorem derived8622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8622 := by
  apply localUnsat_implies_entails f8622 [c8547, c8377, c7849, c8580, c8581, c8585, c8402] c8622 unsat8622 (by rfl) a
  have h0 : Entails.eval a c8547 := derived8547 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c8581 := derived8581 a h
  have h5 : Entails.eval a c8585 := derived8585 a h
  have h6 : Entails.eval a c8402 := derived8402 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8623 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c426, some c841, some c8402, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8623 : lratChecker f8623 p8623 = .success := by decide +kernel
theorem unsat8623 : Unsatisfiable (PosFin 65) f8623 := by
  apply lratCheckerSound f8623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8623
  · intro a ha; simp [p8623] at ha; subst a; trivial
  · exact checked8623
theorem derived8623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8623 := by
  apply localUnsat_implies_entails f8623 [c426, c841, c8402] c8623 unsat8623 (by rfl) a
  have h0 : Entails.eval a c426 := h 425 (by decide)
  have h1 : Entails.eval a c841 := h 840 (by decide)
  have h2 : Entails.eval a c8402 := derived8402 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8624 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8451, some c8591, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8624 : lratChecker f8624 p8624 = .success := by decide +kernel
theorem unsat8624 : Unsatisfiable (PosFin 65) f8624 := by
  apply lratCheckerSound f8624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8624
  · intro a ha; simp [p8624] at ha; subst a; trivial
  · exact checked8624
theorem derived8624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8624 := by
  apply localUnsat_implies_entails f8624 [c8451, c8591] c8624 unsat8624 (by rfl) a
  have h0 : Entails.eval a c8451 := derived8451 a h
  have h1 : Entails.eval a c8591 := derived8591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8625 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8622, some c8623, some c8624, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8625 : lratChecker f8625 p8625 = .success := by decide +kernel
theorem unsat8625 : Unsatisfiable (PosFin 65) f8625 := by
  apply lratCheckerSound f8625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8625
  · intro a ha; simp [p8625] at ha; subst a; trivial
  · exact checked8625
theorem derived8625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8625 := by
  apply localUnsat_implies_entails f8625 [c8377, c7849, c8622, c8623, c8624] c8625 unsat8625 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8622 := derived8622 a h
  have h3 : Entails.eval a c8623 := derived8623 a h
  have h4 : Entails.eval a c8624 := derived8624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8626 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c439, some c422, some c427, some c437, some c440, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8626 : lratChecker f8626 p8626 = .success := by decide +kernel
theorem unsat8626 : Unsatisfiable (PosFin 65) f8626 := by
  apply lratCheckerSound f8626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8626
  · intro a ha; simp [p8626] at ha; subst a; trivial
  · exact checked8626
theorem derived8626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8626 := by
  apply localUnsat_implies_entails f8626 [c439, c422, c427, c437, c440] c8626 unsat8626 (by rfl) a
  have h0 : Entails.eval a c439 := h 438 (by decide)
  have h1 : Entails.eval a c422 := h 421 (by decide)
  have h2 : Entails.eval a c427 := h 426 (by decide)
  have h3 : Entails.eval a c437 := h 436 (by decide)
  have h4 : Entails.eval a c440 := h 439 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8627 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c619, some c8400, some c624, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8627 : lratChecker f8627 p8627 = .success := by decide +kernel
theorem unsat8627 : Unsatisfiable (PosFin 65) f8627 := by
  apply lratCheckerSound f8627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8627
  · intro a ha; simp [p8627] at ha; subst a; trivial
  · exact checked8627
theorem derived8627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8627 := by
  apply localUnsat_implies_entails f8627 [c619, c8400, c624] c8627 unsat8627 (by rfl) a
  have h0 : Entails.eval a c619 := h 618 (by decide)
  have h1 : Entails.eval a c8400 := derived8400 a h
  have h2 : Entails.eval a c624 := h 623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8628 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8626, some c8627, some c8578, some c8580, some c8455, some c1902, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8628 : lratChecker f8628 p8628 = .success := by decide +kernel
theorem unsat8628 : Unsatisfiable (PosFin 65) f8628 := by
  apply lratCheckerSound f8628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8628
  · intro a ha; simp [p8628] at ha; subst a; trivial
  · exact checked8628
theorem derived8628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8628 := by
  apply localUnsat_implies_entails f8628 [c8626, c8627, c8578, c8580, c8455, c1902] c8628 unsat8628 (by rfl) a
  have h0 : Entails.eval a c8626 := derived8626 a h
  have h1 : Entails.eval a c8627 := derived8627 a h
  have h2 : Entails.eval a c8578 := derived8578 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c8455 := derived8455 a h
  have h5 : Entails.eval a c1902 := h 1901 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8629 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c460, some c483, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8629 : lratChecker f8629 p8629 = .success := by decide +kernel
theorem unsat8629 : Unsatisfiable (PosFin 65) f8629 := by
  apply lratCheckerSound f8629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8629
  · intro a ha; simp [p8629] at ha; subst a; trivial
  · exact checked8629
theorem derived8629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8629 := by
  apply localUnsat_implies_entails f8629 [c460, c483] c8629 unsat8629 (by rfl) a
  have h0 : Entails.eval a c460 := h 459 (by decide)
  have h1 : Entails.eval a c483 := h 482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8630 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c562, some c1709, some c2549, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8630 : lratChecker f8630 p8630 = .success := by decide +kernel
theorem unsat8630 : Unsatisfiable (PosFin 65) f8630 := by
  apply lratCheckerSound f8630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8630
  · intro a ha; simp [p8630] at ha; subst a; trivial
  · exact checked8630
theorem derived8630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8630 := by
  apply localUnsat_implies_entails f8630 [c562, c1709, c2549] c8630 unsat8630 (by rfl) a
  have h0 : Entails.eval a c562 := h 561 (by decide)
  have h1 : Entails.eval a c1709 := h 1708 (by decide)
  have h2 : Entails.eval a c2549 := h 2548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8631 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8580, some c8583, some c1873, some c492, some c8630, some c2488, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8631 : lratChecker f8631 p8631 = .success := by decide +kernel
theorem unsat8631 : Unsatisfiable (PosFin 65) f8631 := by
  apply lratCheckerSound f8631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8631
  · intro a ha; simp [p8631] at ha; subst a; trivial
  · exact checked8631
theorem derived8631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8631 := by
  apply localUnsat_implies_entails f8631 [c8580, c8583, c1873, c492, c8630, c2488] c8631 unsat8631 (by rfl) a
  have h0 : Entails.eval a c8580 := derived8580 a h
  have h1 : Entails.eval a c8583 := derived8583 a h
  have h2 : Entails.eval a c1873 := h 1872 (by decide)
  have h3 : Entails.eval a c492 := h 491 (by decide)
  have h4 : Entails.eval a c8630 := derived8630 a h
  have h5 : Entails.eval a c2488 := h 2487 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8632 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8547, some c8621, some c8625, some c8628, some c8580, some c8631, some c8629, some c8578, some c8593, some c2124, some c580, some c1664, some c141, some c1270, some c3404, some c3403, some c3402, some c8079, some c1337, some c81, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8632 : lratChecker f8632 p8632 = .success := by decide +kernel
theorem unsat8632 : Unsatisfiable (PosFin 65) f8632 := by
  apply lratCheckerSound f8632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8632
  · intro a ha; simp [p8632] at ha; subst a; trivial
  · exact checked8632
theorem derived8632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8632 := by
  apply localUnsat_implies_entails f8632 [c7849, c8377, c8547, c8621, c8625, c8628, c8580, c8631, c8629, c8578, c8593, c2124, c580, c1664, c141, c1270, c3404, c3403, c3402, c8079, c1337, c81] c8632 unsat8632 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8621 := derived8621 a h
  have h4 : Entails.eval a c8625 := derived8625 a h
  have h5 : Entails.eval a c8628 := derived8628 a h
  have h6 : Entails.eval a c8580 := derived8580 a h
  have h7 : Entails.eval a c8631 := derived8631 a h
  have h8 : Entails.eval a c8629 := derived8629 a h
  have h9 : Entails.eval a c8578 := derived8578 a h
  have h10 : Entails.eval a c8593 := derived8593 a h
  have h11 : Entails.eval a c2124 := h 2123 (by decide)
  have h12 : Entails.eval a c580 := h 579 (by decide)
  have h13 : Entails.eval a c1664 := h 1663 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c1270 := h 1269 (by decide)
  have h16 : Entails.eval a c3404 := h 3403 (by decide)
  have h17 : Entails.eval a c3403 := h 3402 (by decide)
  have h18 : Entails.eval a c3402 := h 3401 (by decide)
  have h19 : Entails.eval a c8079 := derived8079 a h
  have h20 : Entails.eval a c1337 := h 1336 (by decide)
  have h21 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8633 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2394, some c2379, some c2375, some c2385, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8633 : lratChecker f8633 p8633 = .success := by decide +kernel
theorem unsat8633 : Unsatisfiable (PosFin 65) f8633 := by
  apply lratCheckerSound f8633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8633
  · intro a ha; simp [p8633] at ha; subst a; trivial
  · exact checked8633
theorem derived8633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8633 := by
  apply localUnsat_implies_entails f8633 [c2394, c2379, c2375, c2385] c8633 unsat8633 (by rfl) a
  have h0 : Entails.eval a c2394 := h 2393 (by decide)
  have h1 : Entails.eval a c2379 := h 2378 (by decide)
  have h2 : Entails.eval a c2375 := h 2374 (by decide)
  have h3 : Entails.eval a c2385 := h 2384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8634 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8455, some c1939, some c673, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8634 : lratChecker f8634 p8634 = .success := by decide +kernel
theorem unsat8634 : Unsatisfiable (PosFin 65) f8634 := by
  apply lratCheckerSound f8634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8634
  · intro a ha; simp [p8634] at ha; subst a; trivial
  · exact checked8634
theorem derived8634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8634 := by
  apply localUnsat_implies_entails f8634 [c8455, c1939, c673] c8634 unsat8634 (by rfl) a
  have h0 : Entails.eval a c8455 := derived8455 a h
  have h1 : Entails.eval a c1939 := h 1938 (by decide)
  have h2 : Entails.eval a c673 := h 672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8635 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8634, some c8578, some c8593, some c1956, some c580, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8635 : lratChecker f8635 p8635 = .success := by decide +kernel
theorem unsat8635 : Unsatisfiable (PosFin 65) f8635 := by
  apply lratCheckerSound f8635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8635
  · intro a ha; simp [p8635] at ha; subst a; trivial
  · exact checked8635
theorem derived8635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8635 := by
  apply localUnsat_implies_entails f8635 [c8634, c8578, c8593, c1956, c580] c8635 unsat8635 (by rfl) a
  have h0 : Entails.eval a c8634 := derived8634 a h
  have h1 : Entails.eval a c8578 := derived8578 a h
  have h2 : Entails.eval a c8593 := derived8593 a h
  have h3 : Entails.eval a c1956 := h 1955 (by decide)
  have h4 : Entails.eval a c580 := h 579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8636 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8621, some c8547, some c8377, some c7849, some c8625, some c8628, some c8632, some c8633, some c8629, some c8635, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8636 : lratChecker f8636 p8636 = .success := by decide +kernel
theorem unsat8636 : Unsatisfiable (PosFin 65) f8636 := by
  apply lratCheckerSound f8636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8636
  · intro a ha; simp [p8636] at ha; subst a; trivial
  · exact checked8636
theorem derived8636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8636 := by
  apply localUnsat_implies_entails f8636 [c8621, c8547, c8377, c7849, c8625, c8628, c8632, c8633, c8629, c8635] c8636 unsat8636 (by rfl) a
  have h0 : Entails.eval a c8621 := derived8621 a h
  have h1 : Entails.eval a c8547 := derived8547 a h
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8625 := derived8625 a h
  have h5 : Entails.eval a c8628 := derived8628 a h
  have h6 : Entails.eval a c8632 := derived8632 a h
  have h7 : Entails.eval a c8633 := derived8633 a h
  have h8 : Entails.eval a c8629 := derived8629 a h
  have h9 : Entails.eval a c8635 := derived8635 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8637 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c439, some c428, some c438, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8637 : lratChecker f8637 p8637 = .success := by decide +kernel
theorem unsat8637 : Unsatisfiable (PosFin 65) f8637 := by
  apply lratCheckerSound f8637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8637
  · intro a ha; simp [p8637] at ha; subst a; trivial
  · exact checked8637
theorem derived8637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8637 := by
  apply localUnsat_implies_entails f8637 [c439, c428, c438] c8637 unsat8637 (by rfl) a
  have h0 : Entails.eval a c439 := h 438 (by decide)
  have h1 : Entails.eval a c428 := h 427 (by decide)
  have h2 : Entails.eval a c438 := h 437 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8638 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c461, some c471, some c470, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8638 : lratChecker f8638 p8638 = .success := by decide +kernel
theorem unsat8638 : Unsatisfiable (PosFin 65) f8638 := by
  apply lratCheckerSound f8638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8638
  · intro a ha; simp [p8638] at ha; subst a; trivial
  · exact checked8638
theorem derived8638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8638 := by
  apply localUnsat_implies_entails f8638 [c461, c471, c470] c8638 unsat8638 (by rfl) a
  have h0 : Entails.eval a c461 := h 460 (by decide)
  have h1 : Entails.eval a c471 := h 470 (by decide)
  have h2 : Entails.eval a c470 := h 469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8639 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1856, some c2661, some c1657, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8639 : lratChecker f8639 p8639 = .success := by decide +kernel
theorem unsat8639 : Unsatisfiable (PosFin 65) f8639 := by
  apply lratCheckerSound f8639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8639
  · intro a ha; simp [p8639] at ha; subst a; trivial
  · exact checked8639
theorem derived8639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8639 := by
  apply localUnsat_implies_entails f8639 [c1856, c2661, c1657] c8639 unsat8639 (by rfl) a
  have h0 : Entails.eval a c1856 := h 1855 (by decide)
  have h1 : Entails.eval a c2661 := h 2660 (by decide)
  have h2 : Entails.eval a c1657 := h 1656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8640 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c573, some c572, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8640 : lratChecker f8640 p8640 = .success := by decide +kernel
theorem unsat8640 : Unsatisfiable (PosFin 65) f8640 := by
  apply lratCheckerSound f8640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8640
  · intro a ha; simp [p8640] at ha; subst a; trivial
  · exact checked8640
theorem derived8640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8640 := by
  apply localUnsat_implies_entails f8640 [c573, c572] c8640 unsat8640 (by rfl) a
  have h0 : Entails.eval a c573 := h 572 (by decide)
  have h1 : Entails.eval a c572 := h 571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8641 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8367, some c496, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8641 : lratChecker f8641 p8641 = .success := by decide +kernel
theorem unsat8641 : Unsatisfiable (PosFin 65) f8641 := by
  apply lratCheckerSound f8641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8641
  · intro a ha; simp [p8641] at ha; subst a; trivial
  · exact checked8641
theorem derived8641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8641 := by
  apply localUnsat_implies_entails f8641 [c8367, c496] c8641 unsat8641 (by rfl) a
  have h0 : Entails.eval a c8367 := derived8367 a h
  have h1 : Entails.eval a c496 := h 495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8642 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2570, some c2565, some c2563, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8642 : lratChecker f8642 p8642 = .success := by decide +kernel
theorem unsat8642 : Unsatisfiable (PosFin 65) f8642 := by
  apply lratCheckerSound f8642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8642
  · intro a ha; simp [p8642] at ha; subst a; trivial
  · exact checked8642
theorem derived8642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8642 := by
  apply localUnsat_implies_entails f8642 [c2570, c2565, c2563] c8642 unsat8642 (by rfl) a
  have h0 : Entails.eval a c2570 := h 2569 (by decide)
  have h1 : Entails.eval a c2565 := h 2564 (by decide)
  have h2 : Entails.eval a c2563 := h 2562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8643 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8595, some c8637, some c8638, some c8639, some c8641, some c8642, some c8640, some c2491, some c2484, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8643 : lratChecker f8643 p8643 = .success := by decide +kernel
theorem unsat8643 : Unsatisfiable (PosFin 65) f8643 := by
  apply lratCheckerSound f8643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8643
  · intro a ha; simp [p8643] at ha; subst a; trivial
  · exact checked8643
theorem derived8643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8643 := by
  apply localUnsat_implies_entails f8643 [c8595, c8637, c8638, c8639, c8641, c8642, c8640, c2491, c2484] c8643 unsat8643 (by rfl) a
  have h0 : Entails.eval a c8595 := derived8595 a h
  have h1 : Entails.eval a c8637 := derived8637 a h
  have h2 : Entails.eval a c8638 := derived8638 a h
  have h3 : Entails.eval a c8639 := derived8639 a h
  have h4 : Entails.eval a c8641 := derived8641 a h
  have h5 : Entails.eval a c8642 := derived8642 a h
  have h6 : Entails.eval a c8640 := derived8640 a h
  have h7 : Entails.eval a c2491 := h 2490 (by decide)
  have h8 : Entails.eval a c2484 := h 2483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8644 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c629, some c620, some c628, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8644 : lratChecker f8644 p8644 = .success := by decide +kernel
theorem unsat8644 : Unsatisfiable (PosFin 65) f8644 := by
  apply lratCheckerSound f8644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8644
  · intro a ha; simp [p8644] at ha; subst a; trivial
  · exact checked8644
theorem derived8644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8644 := by
  apply localUnsat_implies_entails f8644 [c629, c620, c628] c8644 unsat8644 (by rfl) a
  have h0 : Entails.eval a c629 := h 628 (by decide)
  have h1 : Entails.eval a c620 := h 619 (by decide)
  have h2 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8645 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8621, some c8636, some c8547, some c8595, some c8643, some c8577, some c8644, some c563, some c1397, some c138, some c1312, some c6750, some c146, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8645 : lratChecker f8645 p8645 = .success := by decide +kernel
theorem unsat8645 : Unsatisfiable (PosFin 65) f8645 := by
  apply lratCheckerSound f8645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8645
  · intro a ha; simp [p8645] at ha; subst a; trivial
  · exact checked8645
theorem derived8645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8645 := by
  apply localUnsat_implies_entails f8645 [c7849, c8377, c8621, c8636, c8547, c8595, c8643, c8577, c8644, c563, c1397, c138, c1312, c6750, c146] c8645 unsat8645 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8621 := derived8621 a h
  have h3 : Entails.eval a c8636 := derived8636 a h
  have h4 : Entails.eval a c8547 := derived8547 a h
  have h5 : Entails.eval a c8595 := derived8595 a h
  have h6 : Entails.eval a c8643 := derived8643 a h
  have h7 : Entails.eval a c8577 := derived8577 a h
  have h8 : Entails.eval a c8644 := derived8644 a h
  have h9 : Entails.eval a c563 := h 562 (by decide)
  have h10 : Entails.eval a c1397 := h 1396 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c1312 := h 1311 (by decide)
  have h13 : Entails.eval a c6750 := derived6750 a h
  have h14 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8646 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8636, some c8621, some c8547, some c8377, some c7849, some c8595, some c8643, some c8577, some c8644, some c8645, some c8641, some c8640, some c8642, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8646 : lratChecker f8646 p8646 = .success := by decide +kernel
theorem unsat8646 : Unsatisfiable (PosFin 65) f8646 := by
  apply lratCheckerSound f8646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8646
  · intro a ha; simp [p8646] at ha; subst a; trivial
  · exact checked8646
theorem derived8646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8646 := by
  apply localUnsat_implies_entails f8646 [c8636, c8621, c8547, c8377, c7849, c8595, c8643, c8577, c8644, c8645, c8641, c8640, c8642] c8646 unsat8646 (by rfl) a
  have h0 : Entails.eval a c8636 := derived8636 a h
  have h1 : Entails.eval a c8621 := derived8621 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8377 := derived8377 a h
  have h4 : Entails.eval a c7849 := derived7849 a h
  have h5 : Entails.eval a c8595 := derived8595 a h
  have h6 : Entails.eval a c8643 := derived8643 a h
  have h7 : Entails.eval a c8577 := derived8577 a h
  have h8 : Entails.eval a c8644 := derived8644 a h
  have h9 : Entails.eval a c8645 := derived8645 a h
  have h10 : Entails.eval a c8641 := derived8641 a h
  have h11 : Entails.eval a c8640 := derived8640 a h
  have h12 : Entails.eval a c8642 := derived8642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8647 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8637, some c8638, some c2392, some c2380, some c2396, some c2387, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8647 : lratChecker f8647 p8647 = .success := by decide +kernel
theorem unsat8647 : Unsatisfiable (PosFin 65) f8647 := by
  apply lratCheckerSound f8647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8647
  · intro a ha; simp [p8647] at ha; subst a; trivial
  · exact checked8647
theorem derived8647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8647 := by
  apply localUnsat_implies_entails f8647 [c8637, c8638, c2392, c2380, c2396, c2387] c8647 unsat8647 (by rfl) a
  have h0 : Entails.eval a c8637 := derived8637 a h
  have h1 : Entails.eval a c8638 := derived8638 a h
  have h2 : Entails.eval a c2392 := h 2391 (by decide)
  have h3 : Entails.eval a c2380 := h 2379 (by decide)
  have h4 : Entails.eval a c2396 := h 2395 (by decide)
  have h5 : Entails.eval a c2387 := h 2386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8648 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1898, some c1903, some c1914, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8648 : lratChecker f8648 p8648 = .success := by decide +kernel
theorem unsat8648 : Unsatisfiable (PosFin 65) f8648 := by
  apply lratCheckerSound f8648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8648
  · intro a ha; simp [p8648] at ha; subst a; trivial
  · exact checked8648
theorem derived8648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8648 := by
  apply localUnsat_implies_entails f8648 [c1898, c1903, c1914] c8648 unsat8648 (by rfl) a
  have h0 : Entails.eval a c1898 := h 1897 (by decide)
  have h1 : Entails.eval a c1903 := h 1902 (by decide)
  have h2 : Entails.eval a c1914 := h 1913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8649 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2251, some c563, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8649 : lratChecker f8649 p8649 = .success := by decide +kernel
theorem unsat8649 : Unsatisfiable (PosFin 65) f8649 := by
  apply lratCheckerSound f8649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8649
  · intro a ha; simp [p8649] at ha; subst a; trivial
  · exact checked8649
theorem derived8649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8649 := by
  apply localUnsat_implies_entails f8649 [c2251, c563] c8649 unsat8649 (by rfl) a
  have h0 : Entails.eval a c2251 := h 2250 (by decide)
  have h1 : Entails.eval a c563 := h 562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8650 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8647, some c8648, some c8644, some c8649, some c8640, some c1952, some c2256, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8650 : lratChecker f8650 p8650 = .success := by decide +kernel
theorem unsat8650 : Unsatisfiable (PosFin 65) f8650 := by
  apply lratCheckerSound f8650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8650
  · intro a ha; simp [p8650] at ha; subst a; trivial
  · exact checked8650
theorem derived8650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8650 := by
  apply localUnsat_implies_entails f8650 [c8647, c8648, c8644, c8649, c8640, c1952, c2256] c8650 unsat8650 (by rfl) a
  have h0 : Entails.eval a c8647 := derived8647 a h
  have h1 : Entails.eval a c8648 := derived8648 a h
  have h2 : Entails.eval a c8644 := derived8644 a h
  have h3 : Entails.eval a c8649 := derived8649 a h
  have h4 : Entails.eval a c8640 := derived8640 a h
  have h5 : Entails.eval a c1952 := h 1951 (by decide)
  have h6 : Entails.eval a c2256 := h 2255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8651 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8636, some c8621, some c8377, some c7849, some c8646, some c8650, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8651 : lratChecker f8651 p8651 = .success := by decide +kernel
theorem unsat8651 : Unsatisfiable (PosFin 65) f8651 := by
  apply lratCheckerSound f8651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8651
  · intro a ha; simp [p8651] at ha; subst a; trivial
  · exact checked8651
theorem derived8651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8651 := by
  apply localUnsat_implies_entails f8651 [c8636, c8621, c8377, c7849, c8646, c8650] c8651 unsat8651 (by rfl) a
  have h0 : Entails.eval a c8636 := derived8636 a h
  have h1 : Entails.eval a c8621 := derived8621 a h
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8646 := derived8646 a h
  have h5 : Entails.eval a c8650 := derived8650 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8652 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c471, some c469, some c480, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8652 : lratChecker f8652 p8652 = .success := by decide +kernel
theorem unsat8652 : Unsatisfiable (PosFin 65) f8652 := by
  apply lratCheckerSound f8652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8652
  · intro a ha; simp [p8652] at ha; subst a; trivial
  · exact checked8652
theorem derived8652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8652 := by
  apply localUnsat_implies_entails f8652 [c471, c469, c480] c8652 unsat8652 (by rfl) a
  have h0 : Entails.eval a c471 := h 470 (by decide)
  have h1 : Entails.eval a c469 := h 468 (by decide)
  have h2 : Entails.eval a c480 := h 479 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8653 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c559, some c561, some c575, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8653 : lratChecker f8653 p8653 = .success := by decide +kernel
theorem unsat8653 : Unsatisfiable (PosFin 65) f8653 := by
  apply lratCheckerSound f8653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8653
  · intro a ha; simp [p8653] at ha; subst a; trivial
  · exact checked8653
theorem derived8653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8653 := by
  apply localUnsat_implies_entails f8653 [c559, c561, c575] c8653 unsat8653 (by rfl) a
  have h0 : Entails.eval a c559 := h 558 (by decide)
  have h1 : Entails.eval a c561 := h 560 (by decide)
  have h2 : Entails.eval a c575 := h 574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8654 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8353, some c587, some c8363, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8654 : lratChecker f8654 p8654 = .success := by decide +kernel
theorem unsat8654 : Unsatisfiable (PosFin 65) f8654 := by
  apply lratCheckerSound f8654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8654
  · intro a ha; simp [p8654] at ha; subst a; trivial
  · exact checked8654
theorem derived8654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8654 := by
  apply localUnsat_implies_entails f8654 [c8353, c587, c8363] c8654 unsat8654 (by rfl) a
  have h0 : Entails.eval a c8353 := derived8353 a h
  have h1 : Entails.eval a c587 := h 586 (by decide)
  have h2 : Entails.eval a c8363 := derived8363 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8655 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8653, some c8654, some c2560, some c2562, some c2575, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8655 : lratChecker f8655 p8655 = .success := by decide +kernel
theorem unsat8655 : Unsatisfiable (PosFin 65) f8655 := by
  apply lratCheckerSound f8655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8655
  · intro a ha; simp [p8655] at ha; subst a; trivial
  · exact checked8655
theorem derived8655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8655 := by
  apply localUnsat_implies_entails f8655 [c8653, c8654, c2560, c2562, c2575] c8655 unsat8655 (by rfl) a
  have h0 : Entails.eval a c8653 := derived8653 a h
  have h1 : Entails.eval a c8654 := derived8654 a h
  have h2 : Entails.eval a c2560 := h 2559 (by decide)
  have h3 : Entails.eval a c2562 := h 2561 (by decide)
  have h4 : Entails.eval a c2575 := h 2574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8656 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8626, some c8595, some c8652, some c8655, some c2486, some c2487, some c2497, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8656 : lratChecker f8656 p8656 = .success := by decide +kernel
theorem unsat8656 : Unsatisfiable (PosFin 65) f8656 := by
  apply lratCheckerSound f8656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8656
  · intro a ha; simp [p8656] at ha; subst a; trivial
  · exact checked8656
theorem derived8656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8656 := by
  apply localUnsat_implies_entails f8656 [c8626, c8595, c8652, c8655, c2486, c2487, c2497] c8656 unsat8656 (by rfl) a
  have h0 : Entails.eval a c8626 := derived8626 a h
  have h1 : Entails.eval a c8595 := derived8595 a h
  have h2 : Entails.eval a c8652 := derived8652 a h
  have h3 : Entails.eval a c8655 := derived8655 a h
  have h4 : Entails.eval a c2486 := h 2485 (by decide)
  have h5 : Entails.eval a c2487 := h 2486 (by decide)
  have h6 : Entails.eval a c2497 := h 2496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8657 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c471, some c470, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8657 : lratChecker f8657 p8657 = .success := by decide +kernel
theorem unsat8657 : Unsatisfiable (PosFin 65) f8657 := by
  apply lratCheckerSound f8657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8657
  · intro a ha; simp [p8657] at ha; subst a; trivial
  · exact checked8657
theorem derived8657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8657 := by
  apply localUnsat_implies_entails f8657 [c471, c470] c8657 unsat8657 (by rfl) a
  have h0 : Entails.eval a c471 := h 470 (by decide)
  have h1 : Entails.eval a c470 := h 469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8658 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8595, some c8626, some c8656, some c8641, some c8642, some c8640, some c8657, some c2488, some c2491, some c2492, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8658 : lratChecker f8658 p8658 = .success := by decide +kernel
theorem unsat8658 : Unsatisfiable (PosFin 65) f8658 := by
  apply lratCheckerSound f8658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8658
  · intro a ha; simp [p8658] at ha; subst a; trivial
  · exact checked8658
theorem derived8658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8658 := by
  apply localUnsat_implies_entails f8658 [c8595, c8626, c8656, c8641, c8642, c8640, c8657, c2488, c2491, c2492] c8658 unsat8658 (by rfl) a
  have h0 : Entails.eval a c8595 := derived8595 a h
  have h1 : Entails.eval a c8626 := derived8626 a h
  have h2 : Entails.eval a c8656 := derived8656 a h
  have h3 : Entails.eval a c8641 := derived8641 a h
  have h4 : Entails.eval a c8642 := derived8642 a h
  have h5 : Entails.eval a c8640 := derived8640 a h
  have h6 : Entails.eval a c8657 := derived8657 a h
  have h7 : Entails.eval a c2488 := h 2487 (by decide)
  have h8 : Entails.eval a c2491 := h 2490 (by decide)
  have h9 : Entails.eval a c2492 := h 2491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8659 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8595, some c8658, some c8593, some c8578, some c8654, some c2152, some c2156, some c2173, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8659 : lratChecker f8659 p8659 = .success := by decide +kernel
theorem unsat8659 : Unsatisfiable (PosFin 65) f8659 := by
  apply lratCheckerSound f8659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8659
  · intro a ha; simp [p8659] at ha; subst a; trivial
  · exact checked8659
theorem derived8659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8659 := by
  apply localUnsat_implies_entails f8659 [c8595, c8658, c8593, c8578, c8654, c2152, c2156, c2173] c8659 unsat8659 (by rfl) a
  have h0 : Entails.eval a c8595 := derived8595 a h
  have h1 : Entails.eval a c8658 := derived8658 a h
  have h2 : Entails.eval a c8593 := derived8593 a h
  have h3 : Entails.eval a c8578 := derived8578 a h
  have h4 : Entails.eval a c8654 := derived8654 a h
  have h5 : Entails.eval a c2152 := h 2151 (by decide)
  have h6 : Entails.eval a c2156 := h 2155 (by decide)
  have h7 : Entails.eval a c2173 := h 2172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8660 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8652, some c2392, some c2402, some c2389, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8660 : lratChecker f8660 p8660 = .success := by decide +kernel
theorem unsat8660 : Unsatisfiable (PosFin 65) f8660 := by
  apply lratCheckerSound f8660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8660
  · intro a ha; simp [p8660] at ha; subst a; trivial
  · exact checked8660
theorem derived8660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8660 := by
  apply localUnsat_implies_entails f8660 [c8652, c2392, c2402, c2389] c8660 unsat8660 (by rfl) a
  have h0 : Entails.eval a c8652 := derived8652 a h
  have h1 : Entails.eval a c2392 := h 2391 (by decide)
  have h2 : Entails.eval a c2402 := h 2401 (by decide)
  have h3 : Entails.eval a c2389 := h 2388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8661 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8660, some c8657, some c2392, some c2390, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8661 : lratChecker f8661 p8661 = .success := by decide +kernel
theorem unsat8661 : Unsatisfiable (PosFin 65) f8661 := by
  apply lratCheckerSound f8661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8661
  · intro a ha; simp [p8661] at ha; subst a; trivial
  · exact checked8661
theorem derived8661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8661 := by
  apply localUnsat_implies_entails f8661 [c8660, c8657, c2392, c2390] c8661 unsat8661 (by rfl) a
  have h0 : Entails.eval a c8660 := derived8660 a h
  have h1 : Entails.eval a c8657 := derived8657 a h
  have h2 : Entails.eval a c2392 := h 2391 (by decide)
  have h3 : Entails.eval a c2390 := h 2389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8662 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8659, some c8626, some c8661, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8662 : lratChecker f8662 p8662 = .success := by decide +kernel
theorem unsat8662 : Unsatisfiable (PosFin 65) f8662 := by
  apply lratCheckerSound f8662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8662
  · intro a ha; simp [p8662] at ha; subst a; trivial
  · exact checked8662
theorem derived8662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8662 := by
  apply localUnsat_implies_entails f8662 [c8659, c8626, c8661] c8662 unsat8662 (by rfl) a
  have h0 : Entails.eval a c8659 := derived8659 a h
  have h1 : Entails.eval a c8626 := derived8626 a h
  have h2 : Entails.eval a c8661 := derived8661 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8663 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c619, some c615, some c637, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8663 : lratChecker f8663 p8663 = .success := by decide +kernel
theorem unsat8663 : Unsatisfiable (PosFin 65) f8663 := by
  apply lratCheckerSound f8663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8663
  · intro a ha; simp [p8663] at ha; subst a; trivial
  · exact checked8663
theorem derived8663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8663 := by
  apply localUnsat_implies_entails f8663 [c619, c615, c637] c8663 unsat8663 (by rfl) a
  have h0 : Entails.eval a c619 := h 618 (by decide)
  have h1 : Entails.eval a c615 := h 614 (by decide)
  have h2 : Entails.eval a c637 := h 636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8664 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8547, some c8621, some c8636, some c8651, some c8662, some c8659, some c8620, some c8663, some c1917, some c1913, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8664 : lratChecker f8664 p8664 = .success := by decide +kernel
theorem unsat8664 : Unsatisfiable (PosFin 65) f8664 := by
  apply lratCheckerSound f8664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8664
  · intro a ha; simp [p8664] at ha; subst a; trivial
  · exact checked8664
theorem derived8664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8664 := by
  apply localUnsat_implies_entails f8664 [c7849, c8377, c8547, c8621, c8636, c8651, c8662, c8659, c8620, c8663, c1917, c1913] c8664 unsat8664 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8621 := derived8621 a h
  have h4 : Entails.eval a c8636 := derived8636 a h
  have h5 : Entails.eval a c8651 := derived8651 a h
  have h6 : Entails.eval a c8662 := derived8662 a h
  have h7 : Entails.eval a c8659 := derived8659 a h
  have h8 : Entails.eval a c8620 := derived8620 a h
  have h9 : Entails.eval a c8663 := derived8663 a h
  have h10 : Entails.eval a c1917 := h 1916 (by decide)
  have h11 : Entails.eval a c1913 := h 1912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8665 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c629, some c628, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8665 : lratChecker f8665 p8665 = .success := by decide +kernel
theorem unsat8665 : Unsatisfiable (PosFin 65) f8665 := by
  apply lratCheckerSound f8665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8665
  · intro a ha; simp [p8665] at ha; subst a; trivial
  · exact checked8665
theorem derived8665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8665 := by
  apply localUnsat_implies_entails f8665 [c629, c628] c8665 unsat8665 (by rfl) a
  have h0 : Entails.eval a c629 := h 628 (by decide)
  have h1 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8666 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8547, some c8621, some c8636, some c8651, some c8662, some c8659, some c8664, some c8665, some c1917, some c1914, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8666 : lratChecker f8666 p8666 = .success := by decide +kernel
theorem unsat8666 : Unsatisfiable (PosFin 65) f8666 := by
  apply lratCheckerSound f8666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8666
  · intro a ha; simp [p8666] at ha; subst a; trivial
  · exact checked8666
theorem derived8666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8666 := by
  apply localUnsat_implies_entails f8666 [c7849, c8377, c8547, c8621, c8636, c8651, c8662, c8659, c8664, c8665, c1917, c1914] c8666 unsat8666 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8621 := derived8621 a h
  have h4 : Entails.eval a c8636 := derived8636 a h
  have h5 : Entails.eval a c8651 := derived8651 a h
  have h6 : Entails.eval a c8662 := derived8662 a h
  have h7 : Entails.eval a c8659 := derived8659 a h
  have h8 : Entails.eval a c8664 := derived8664 a h
  have h9 : Entails.eval a c8665 := derived8665 a h
  have h10 : Entails.eval a c1917 := h 1916 (by decide)
  have h11 : Entails.eval a c1914 := h 1913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8667 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8662, some c8659, some c1952, some c2250, some c2389, some c823, some c2049, some c2575, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8667 : lratChecker f8667 p8667 = .success := by decide +kernel
theorem unsat8667 : Unsatisfiable (PosFin 65) f8667 := by
  apply lratCheckerSound f8667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8667
  · intro a ha; simp [p8667] at ha; subst a; trivial
  · exact checked8667
theorem derived8667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8667 := by
  apply localUnsat_implies_entails f8667 [c8662, c8659, c1952, c2250, c2389, c823, c2049, c2575] c8667 unsat8667 (by rfl) a
  have h0 : Entails.eval a c8662 := derived8662 a h
  have h1 : Entails.eval a c8659 := derived8659 a h
  have h2 : Entails.eval a c1952 := h 1951 (by decide)
  have h3 : Entails.eval a c2250 := h 2249 (by decide)
  have h4 : Entails.eval a c2389 := h 2388 (by decide)
  have h5 : Entails.eval a c823 := h 822 (by decide)
  have h6 : Entails.eval a c2049 := h 2048 (by decide)
  have h7 : Entails.eval a c2575 := h 2574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8668 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8666, some c7849, some c8377, some c8547, some c8621, some c8636, some c8651, some c8662, some c8659, some c8620, some c8667, some c8653, some c1917, some c1913, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8668 : lratChecker f8668 p8668 = .success := by decide +kernel
theorem unsat8668 : Unsatisfiable (PosFin 65) f8668 := by
  apply lratCheckerSound f8668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8668
  · intro a ha; simp [p8668] at ha; subst a; trivial
  · exact checked8668
theorem derived8668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8668 := by
  apply localUnsat_implies_entails f8668 [c8666, c7849, c8377, c8547, c8621, c8636, c8651, c8662, c8659, c8620, c8667, c8653, c1917, c1913] c8668 unsat8668 (by rfl) a
  have h0 : Entails.eval a c8666 := derived8666 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c8547 := derived8547 a h
  have h4 : Entails.eval a c8621 := derived8621 a h
  have h5 : Entails.eval a c8636 := derived8636 a h
  have h6 : Entails.eval a c8651 := derived8651 a h
  have h7 : Entails.eval a c8662 := derived8662 a h
  have h8 : Entails.eval a c8659 := derived8659 a h
  have h9 : Entails.eval a c8620 := derived8620 a h
  have h10 : Entails.eval a c8667 := derived8667 a h
  have h11 : Entails.eval a c8653 := derived8653 a h
  have h12 : Entails.eval a c1917 := h 1916 (by decide)
  have h13 : Entails.eval a c1913 := h 1912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8669 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨28, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1952, some c2256, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8669 : lratChecker f8669 p8669 = .success := by decide +kernel
theorem unsat8669 : Unsatisfiable (PosFin 65) f8669 := by
  apply lratCheckerSound f8669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8669
  · intro a ha; simp [p8669] at ha; subst a; trivial
  · exact checked8669
theorem derived8669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8669 := by
  apply localUnsat_implies_entails f8669 [c1952, c2256] c8669 unsat8669 (by rfl) a
  have h0 : Entails.eval a c1952 := h 1951 (by decide)
  have h1 : Entails.eval a c2256 := h 2255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8670 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8547, some c8621, some c8636, some c8651, some c8659, some c8662, some c8666, some c8668, some c8669, some c8640, some c1917, some c1914, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8670 : lratChecker f8670 p8670 = .success := by decide +kernel
theorem unsat8670 : Unsatisfiable (PosFin 65) f8670 := by
  apply lratCheckerSound f8670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8670
  · intro a ha; simp [p8670] at ha; subst a; trivial
  · exact checked8670
theorem derived8670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8670 := by
  apply localUnsat_implies_entails f8670 [c7849, c8377, c8547, c8621, c8636, c8651, c8659, c8662, c8666, c8668, c8669, c8640, c1917, c1914] c8670 unsat8670 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8621 := derived8621 a h
  have h4 : Entails.eval a c8636 := derived8636 a h
  have h5 : Entails.eval a c8651 := derived8651 a h
  have h6 : Entails.eval a c8659 := derived8659 a h
  have h7 : Entails.eval a c8662 := derived8662 a h
  have h8 : Entails.eval a c8666 := derived8666 a h
  have h9 : Entails.eval a c8668 := derived8668 a h
  have h10 : Entails.eval a c8669 := derived8669 a h
  have h11 : Entails.eval a c8640 := derived8640 a h
  have h12 : Entails.eval a c1917 := h 1916 (by decide)
  have h13 : Entails.eval a c1914 := h 1913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8671 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c289, some c288, some c7488, some c6690, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8671 : lratChecker f8671 p8671 = .success := by decide +kernel
theorem unsat8671 : Unsatisfiable (PosFin 65) f8671 := by
  apply lratCheckerSound f8671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8671
  · intro a ha; simp [p8671] at ha; subst a; trivial
  · exact checked8671
theorem derived8671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8671 := by
  apply localUnsat_implies_entails f8671 [c289, c288, c7488, c6690] c8671 unsat8671 (by rfl) a
  have h0 : Entails.eval a c289 := h 288 (by decide)
  have h1 : Entails.eval a c288 := h 287 (by decide)
  have h2 : Entails.eval a c7488 := derived7488 a h
  have h3 : Entails.eval a c6690 := derived6690 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8672 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c322, some c300, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8672 : lratChecker f8672 p8672 = .success := by decide +kernel
theorem unsat8672 : Unsatisfiable (PosFin 65) f8672 := by
  apply lratCheckerSound f8672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8672
  · intro a ha; simp [p8672] at ha; subst a; trivial
  · exact checked8672
theorem derived8672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8672 := by
  apply localUnsat_implies_entails f8672 [c322, c300] c8672 unsat8672 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8673 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8671, some c7208, some c7492, some c7564, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8673 : lratChecker f8673 p8673 = .success := by decide +kernel
theorem unsat8673 : Unsatisfiable (PosFin 65) f8673 := by
  apply lratCheckerSound f8673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8673
  · intro a ha; simp [p8673] at ha; subst a; trivial
  · exact checked8673
theorem derived8673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8673 := by
  apply localUnsat_implies_entails f8673 [c8671, c7208, c7492, c7564] c8673 unsat8673 (by rfl) a
  have h0 : Entails.eval a c8671 := derived8671 a h
  have h1 : Entails.eval a c7208 := derived7208 a h
  have h2 : Entails.eval a c7492 := derived7492 a h
  have h3 : Entails.eval a c7564 := derived7564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8674 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7340, some c7492, some c7368, some c7356, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8674 : lratChecker f8674 p8674 = .success := by decide +kernel
theorem unsat8674 : Unsatisfiable (PosFin 65) f8674 := by
  apply lratCheckerSound f8674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8674
  · intro a ha; simp [p8674] at ha; subst a; trivial
  · exact checked8674
theorem derived8674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8674 := by
  apply localUnsat_implies_entails f8674 [c7340, c7492, c7368, c7356] c8674 unsat8674 (by rfl) a
  have h0 : Entails.eval a c7340 := derived7340 a h
  have h1 : Entails.eval a c7492 := derived7492 a h
  have h2 : Entails.eval a c7368 := derived7368 a h
  have h3 : Entails.eval a c7356 := derived7356 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8675 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7208, some c7492, some c7564, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8675 : lratChecker f8675 p8675 = .success := by decide +kernel
theorem unsat8675 : Unsatisfiable (PosFin 65) f8675 := by
  apply lratCheckerSound f8675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8675
  · intro a ha; simp [p8675] at ha; subst a; trivial
  · exact checked8675
theorem derived8675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8675 := by
  apply localUnsat_implies_entails f8675 [c7208, c7492, c7564] c8675 unsat8675 (by rfl) a
  have h0 : Entails.eval a c7208 := derived7208 a h
  have h1 : Entails.eval a c7492 := derived7492 a h
  have h2 : Entails.eval a c7564 := derived7564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8676 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8672, some c8675, some c7338, some c991, some c996, some c989, some c988, some c995, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8676 : lratChecker f8676 p8676 = .success := by decide +kernel
theorem unsat8676 : Unsatisfiable (PosFin 65) f8676 := by
  apply lratCheckerSound f8676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8676
  · intro a ha; simp [p8676] at ha; subst a; trivial
  · exact checked8676
theorem derived8676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8676 := by
  apply localUnsat_implies_entails f8676 [c8672, c8675, c7338, c991, c996, c989, c988, c995] c8676 unsat8676 (by rfl) a
  have h0 : Entails.eval a c8672 := derived8672 a h
  have h1 : Entails.eval a c8675 := derived8675 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  have h3 : Entails.eval a c991 := h 990 (by decide)
  have h4 : Entails.eval a c996 := h 995 (by decide)
  have h5 : Entails.eval a c989 := h 988 (by decide)
  have h6 : Entails.eval a c988 := h 987 (by decide)
  have h7 : Entails.eval a c995 := h 994 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8677 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2137, some c998, some c285, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8677 : lratChecker f8677 p8677 = .success := by decide +kernel
theorem unsat8677 : Unsatisfiable (PosFin 65) f8677 := by
  apply lratCheckerSound f8677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8677
  · intro a ha; simp [p8677] at ha; subst a; trivial
  · exact checked8677
theorem derived8677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8677 := by
  apply localUnsat_implies_entails f8677 [c2137, c998, c285] c8677 unsat8677 (by rfl) a
  have h0 : Entails.eval a c2137 := h 2136 (by decide)
  have h1 : Entails.eval a c998 := h 997 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8678 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8673, some c997, some c309, some c7338, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8678 : lratChecker f8678 p8678 = .success := by decide +kernel
theorem unsat8678 : Unsatisfiable (PosFin 65) f8678 := by
  apply lratCheckerSound f8678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8678
  · intro a ha; simp [p8678] at ha; subst a; trivial
  · exact checked8678
theorem derived8678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8678 := by
  apply localUnsat_implies_entails f8678 [c8673, c997, c309, c7338] c8678 unsat8678 (by rfl) a
  have h0 : Entails.eval a c8673 := derived8673 a h
  have h1 : Entails.eval a c997 := h 996 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c7338 := derived7338 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8679 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c319, some c324, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8679 : lratChecker f8679 p8679 = .success := by decide +kernel
theorem unsat8679 : Unsatisfiable (PosFin 65) f8679 := by
  apply lratCheckerSound f8679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8679
  · intro a ha; simp [p8679] at ha; subst a; trivial
  · exact checked8679
theorem derived8679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8679 := by
  apply localUnsat_implies_entails f8679 [c319, c324] c8679 unsat8679 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8680 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8679, some c8675, some c7338, some c990, some c994, some c988, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8680 : lratChecker f8680 p8680 = .success := by decide +kernel
theorem unsat8680 : Unsatisfiable (PosFin 65) f8680 := by
  apply lratCheckerSound f8680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8680
  · intro a ha; simp [p8680] at ha; subst a; trivial
  · exact checked8680
theorem derived8680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8680 := by
  apply localUnsat_implies_entails f8680 [c8679, c8675, c7338, c990, c994, c988] c8680 unsat8680 (by rfl) a
  have h0 : Entails.eval a c8679 := derived8679 a h
  have h1 : Entails.eval a c8675 := derived8675 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  have h3 : Entails.eval a c990 := h 989 (by decide)
  have h4 : Entails.eval a c994 := h 993 (by decide)
  have h5 : Entails.eval a c988 := h 987 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8680

end CochromaticTwenty.Certificates.FixedCore1
