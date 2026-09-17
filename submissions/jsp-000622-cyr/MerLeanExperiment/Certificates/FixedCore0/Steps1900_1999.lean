import MerLeanExperiment.Certificates.FixedCore0.Steps1800_1899

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9451 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9449, some c9215, some c9445, some c9450, some c1422, some c9441, some c2477, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9451 : lratChecker f9451 p9451 = .success := by decide +kernel
theorem unsat9451 : Unsatisfiable (PosFin 65) f9451 := by
  apply lratCheckerSound f9451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9451
  · intro a ha; simp [p9451] at ha; subst a; trivial
  · exact checked9451
theorem derived9451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9451 := by
  apply localUnsat_implies_entails f9451 [c9347, c9449, c9215, c9445, c9450, c1422, c9441, c2477] c9451 unsat9451 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9449 := derived9449 a h
  have h2 : Entails.eval a c9215 := derived9215 a h
  have h3 : Entails.eval a c9445 := derived9445 a h
  have h4 : Entails.eval a c9450 := derived9450 a h
  have h5 : Entails.eval a c1422 := h 1421 (by decide)
  have h6 : Entails.eval a c9441 := derived9441 a h
  have h7 : Entails.eval a c2477 := h 2476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9452 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨62, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9325, some c3337, some c8007, some c3648, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9452 : lratChecker f9452 p9452 = .success := by decide +kernel
theorem unsat9452 : Unsatisfiable (PosFin 65) f9452 := by
  apply lratCheckerSound f9452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9452
  · intro a ha; simp [p9452] at ha; subst a; trivial
  · exact checked9452
theorem derived9452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9452 := by
  apply localUnsat_implies_entails f9452 [c9325, c3337, c8007, c3648] c9452 unsat9452 (by rfl) a
  have h0 : Entails.eval a c9325 := derived9325 a h
  have h1 : Entails.eval a c3337 := h 3336 (by decide)
  have h2 : Entails.eval a c8007 := derived8007 a h
  have h3 : Entails.eval a c3648 := h 3647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9453 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨63, by decide⟩, true), (⟨10, by decide⟩, false), (⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨62, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c363, some c358, some c361, some c6197, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p9453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9453 : lratChecker f9453 p9453 = .success := by decide +kernel
theorem unsat9453 : Unsatisfiable (PosFin 65) f9453 := by
  apply lratCheckerSound f9453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9453
  · intro a ha; simp [p9453] at ha; subst a; trivial
  · exact checked9453
theorem derived9453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9453 := by
  apply localUnsat_implies_entails f9453 [c363, c358, c361, c6197] c9453 unsat9453 (by rfl) a
  have h0 : Entails.eval a c363 := h 362 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c6197 := h 6196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9454 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨16, by decide⟩, false), (⟨63, by decide⟩, true), (⟨10, by decide⟩, false), (⟨62, by decide⟩, true), (⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8395, some c357, some c5643, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9454 : lratChecker f9454 p9454 = .success := by decide +kernel
theorem unsat9454 : Unsatisfiable (PosFin 65) f9454 := by
  apply lratCheckerSound f9454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9454
  · intro a ha; simp [p9454] at ha; subst a; trivial
  · exact checked9454
theorem derived9454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9454 := by
  apply localUnsat_implies_entails f9454 [c8395, c357, c5643] c9454 unsat9454 (by rfl) a
  have h0 : Entails.eval a c8395 := derived8395 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c5643 := h 5642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9455 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9443, some c9419, some c9347, some c9446, some c9451, some c9212, some c1433, some c9445, some c9452, some c9256, some c9257, some c3630, some c3806, some c3818, some c4043, some c2480, some c3812, some c4258, some c9453, some c9454, some c1412, some c5494, some c3803, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9455 : lratChecker f9455 p9455 = .success := by decide +kernel
theorem unsat9455 : Unsatisfiable (PosFin 65) f9455 := by
  apply lratCheckerSound f9455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9455
  · intro a ha; simp [p9455] at ha; subst a; trivial
  · exact checked9455
theorem derived9455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9455 := by
  apply localUnsat_implies_entails f9455 [c9443, c9419, c9347, c9446, c9451, c9212, c1433, c9445, c9452, c9256, c9257, c3630, c3806, c3818, c4043, c2480, c3812, c4258, c9453, c9454, c1412, c5494, c3803] c9455 unsat9455 (by rfl) a
  have h0 : Entails.eval a c9443 := derived9443 a h
  have h1 : Entails.eval a c9419 := derived9419 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9446 := derived9446 a h
  have h4 : Entails.eval a c9451 := derived9451 a h
  have h5 : Entails.eval a c9212 := derived9212 a h
  have h6 : Entails.eval a c1433 := h 1432 (by decide)
  have h7 : Entails.eval a c9445 := derived9445 a h
  have h8 : Entails.eval a c9452 := derived9452 a h
  have h9 : Entails.eval a c9256 := derived9256 a h
  have h10 : Entails.eval a c9257 := derived9257 a h
  have h11 : Entails.eval a c3630 := h 3629 (by decide)
  have h12 : Entails.eval a c3806 := h 3805 (by decide)
  have h13 : Entails.eval a c3818 := h 3817 (by decide)
  have h14 : Entails.eval a c4043 := h 4042 (by decide)
  have h15 : Entails.eval a c2480 := h 2479 (by decide)
  have h16 : Entails.eval a c3812 := h 3811 (by decide)
  have h17 : Entails.eval a c4258 := h 4257 (by decide)
  have h18 : Entails.eval a c9453 := derived9453 a h
  have h19 : Entails.eval a c9454 := derived9454 a h
  have h20 : Entails.eval a c1412 := h 1411 (by decide)
  have h21 : Entails.eval a c5494 := h 5493 (by decide)
  have h22 : Entails.eval a c3803 := h 3802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9456 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨58, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2677, some c2678, some c2686, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9456 : lratChecker f9456 p9456 = .success := by decide +kernel
theorem unsat9456 : Unsatisfiable (PosFin 65) f9456 := by
  apply lratCheckerSound f9456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9456
  · intro a ha; simp [p9456] at ha; subst a; trivial
  · exact checked9456
theorem derived9456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9456 := by
  apply localUnsat_implies_entails f9456 [c2677, c2678, c2686] c9456 unsat9456 (by rfl) a
  have h0 : Entails.eval a c2677 := h 2676 (by decide)
  have h1 : Entails.eval a c2678 := h 2677 (by decide)
  have h2 : Entails.eval a c2686 := h 2685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9457 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3245, some c3242, some c3246, some c9225, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9457 : lratChecker f9457 p9457 = .success := by decide +kernel
theorem unsat9457 : Unsatisfiable (PosFin 65) f9457 := by
  apply lratCheckerSound f9457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9457
  · intro a ha; simp [p9457] at ha; subst a; trivial
  · exact checked9457
theorem derived9457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9457 := by
  apply localUnsat_implies_entails f9457 [c3245, c3242, c3246, c9225] c9457 unsat9457 (by rfl) a
  have h0 : Entails.eval a c3245 := h 3244 (by decide)
  have h1 : Entails.eval a c3242 := h 3241 (by decide)
  have h2 : Entails.eval a c3246 := h 3245 (by decide)
  have h3 : Entails.eval a c9225 := derived9225 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9458 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c3590, some c3594, some c1383, some c2882, some c4679, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9458 : lratChecker f9458 p9458 = .success := by decide +kernel
theorem unsat9458 : Unsatisfiable (PosFin 65) f9458 := by
  apply lratCheckerSound f9458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9458
  · intro a ha; simp [p9458] at ha; subst a; trivial
  · exact checked9458
theorem derived9458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9458 := by
  apply localUnsat_implies_entails f9458 [c9347, c3590, c3594, c1383, c2882, c4679] c9458 unsat9458 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c3590 := h 3589 (by decide)
  have h2 : Entails.eval a c3594 := h 3593 (by decide)
  have h3 : Entails.eval a c1383 := h 1382 (by decide)
  have h4 : Entails.eval a c2882 := h 2881 (by decide)
  have h5 : Entails.eval a c4679 := h 4678 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9459 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9458, some c4458, some c4296, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9459 : lratChecker f9459 p9459 = .success := by decide +kernel
theorem unsat9459 : Unsatisfiable (PosFin 65) f9459 := by
  apply lratCheckerSound f9459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9459
  · intro a ha; simp [p9459] at ha; subst a; trivial
  · exact checked9459
theorem derived9459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9459 := by
  apply localUnsat_implies_entails f9459 [c9458, c4458, c4296] c9459 unsat9459 (by rfl) a
  have h0 : Entails.eval a c9458 := derived9458 a h
  have h1 : Entails.eval a c4458 := h 4457 (by decide)
  have h2 : Entails.eval a c4296 := h 4295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9460 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9455, some c9443, some c9419, some c9347, some c9456, some c9457, some c9447, some c9459, some c9406, some c2845, some c9452, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9460 : lratChecker f9460 p9460 = .success := by decide +kernel
theorem unsat9460 : Unsatisfiable (PosFin 65) f9460 := by
  apply lratCheckerSound f9460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9460
  · intro a ha; simp [p9460] at ha; subst a; trivial
  · exact checked9460
theorem derived9460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9460 := by
  apply localUnsat_implies_entails f9460 [c9455, c9443, c9419, c9347, c9456, c9457, c9447, c9459, c9406, c2845, c9452] c9460 unsat9460 (by rfl) a
  have h0 : Entails.eval a c9455 := derived9455 a h
  have h1 : Entails.eval a c9443 := derived9443 a h
  have h2 : Entails.eval a c9419 := derived9419 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9456 := derived9456 a h
  have h5 : Entails.eval a c9457 := derived9457 a h
  have h6 : Entails.eval a c9447 := derived9447 a h
  have h7 : Entails.eval a c9459 := derived9459 a h
  have h8 : Entails.eval a c9406 := derived9406 a h
  have h9 : Entails.eval a c2845 := h 2844 (by decide)
  have h10 : Entails.eval a c9452 := derived9452 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9461 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2682, some c4726, some c4627, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9461 : lratChecker f9461 p9461 = .success := by decide +kernel
theorem unsat9461 : Unsatisfiable (PosFin 65) f9461 := by
  apply lratCheckerSound f9461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9461
  · intro a ha; simp [p9461] at ha; subst a; trivial
  · exact checked9461
theorem derived9461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9461 := by
  apply localUnsat_implies_entails f9461 [c2682, c4726, c4627] c9461 unsat9461 (by rfl) a
  have h0 : Entails.eval a c2682 := h 2681 (by decide)
  have h1 : Entails.eval a c4726 := h 4725 (by decide)
  have h2 : Entails.eval a c4627 := h 4626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9462 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9455, some c9443, some c9419, some c9347, some c9460, some c9212, some c9461, some c9459, some c9406, some c2845, some c9452, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9462 : lratChecker f9462 p9462 = .success := by decide +kernel
theorem unsat9462 : Unsatisfiable (PosFin 65) f9462 := by
  apply lratCheckerSound f9462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9462
  · intro a ha; simp [p9462] at ha; subst a; trivial
  · exact checked9462
theorem derived9462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9462 := by
  apply localUnsat_implies_entails f9462 [c9455, c9443, c9419, c9347, c9460, c9212, c9461, c9459, c9406, c2845, c9452] c9462 unsat9462 (by rfl) a
  have h0 : Entails.eval a c9455 := derived9455 a h
  have h1 : Entails.eval a c9443 := derived9443 a h
  have h2 : Entails.eval a c9419 := derived9419 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9460 := derived9460 a h
  have h5 : Entails.eval a c9212 := derived9212 a h
  have h6 : Entails.eval a c9461 := derived9461 a h
  have h7 : Entails.eval a c9459 := derived9459 a h
  have h8 : Entails.eval a c9406 := derived9406 a h
  have h9 : Entails.eval a c2845 := h 2844 (by decide)
  have h10 : Entails.eval a c9452 := derived9452 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9463 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9458, some c9406, some c2845, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9463 : lratChecker f9463 p9463 = .success := by decide +kernel
theorem unsat9463 : Unsatisfiable (PosFin 65) f9463 := by
  apply lratCheckerSound f9463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9463
  · intro a ha; simp [p9463] at ha; subst a; trivial
  · exact checked9463
theorem derived9463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9463 := by
  apply localUnsat_implies_entails f9463 [c9347, c9458, c9406, c2845] c9463 unsat9463 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9458 := derived9458 a h
  have h2 : Entails.eval a c9406 := derived9406 a h
  have h3 : Entails.eval a c2845 := h 2844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9464 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨62, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3577, some c9441, some c4310, some c4467, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9464 : lratChecker f9464 p9464 = .success := by decide +kernel
theorem unsat9464 : Unsatisfiable (PosFin 65) f9464 := by
  apply lratCheckerSound f9464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9464
  · intro a ha; simp [p9464] at ha; subst a; trivial
  · exact checked9464
theorem derived9464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9464 := by
  apply localUnsat_implies_entails f9464 [c3577, c9441, c4310, c4467] c9464 unsat9464 (by rfl) a
  have h0 : Entails.eval a c3577 := h 3576 (by decide)
  have h1 : Entails.eval a c9441 := derived9441 a h
  have h2 : Entails.eval a c4310 := h 4309 (by decide)
  have h3 : Entails.eval a c4467 := h 4466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9465 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c9462, some c9215, some c9455, some c9443, some c9347, some c9456, some c9249, some c9463, some c9464, some c9416, some c2477, some c3644, some c3339, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9465 : lratChecker f9465 p9465 = .success := by decide +kernel
theorem unsat9465 : Unsatisfiable (PosFin 65) f9465 := by
  apply lratCheckerSound f9465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9465
  · intro a ha; simp [p9465] at ha; subst a; trivial
  · exact checked9465
theorem derived9465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9465 := by
  apply localUnsat_implies_entails f9465 [c9419, c9462, c9215, c9455, c9443, c9347, c9456, c9249, c9463, c9464, c9416, c2477, c3644, c3339] c9465 unsat9465 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c9462 := derived9462 a h
  have h2 : Entails.eval a c9215 := derived9215 a h
  have h3 : Entails.eval a c9455 := derived9455 a h
  have h4 : Entails.eval a c9443 := derived9443 a h
  have h5 : Entails.eval a c9347 := derived9347 a h
  have h6 : Entails.eval a c9456 := derived9456 a h
  have h7 : Entails.eval a c9249 := derived9249 a h
  have h8 : Entails.eval a c9463 := derived9463 a h
  have h9 : Entails.eval a c9464 := derived9464 a h
  have h10 : Entails.eval a c9416 := derived9416 a h
  have h11 : Entails.eval a c2477 := h 2476 (by decide)
  have h12 : Entails.eval a c3644 := h 3643 (by decide)
  have h13 : Entails.eval a c3339 := h 3338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9466 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c9347, some c9443, some c9455, some c9462, some c9215, some c9465, some c9256, some c9257, some c3630, some c3653, some c3633, some c3664, some c4043, some c2886, some c3652, some c4258, some c5009, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9466 : lratChecker f9466 p9466 = .success := by decide +kernel
theorem unsat9466 : Unsatisfiable (PosFin 65) f9466 := by
  apply lratCheckerSound f9466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9466
  · intro a ha; simp [p9466] at ha; subst a; trivial
  · exact checked9466
theorem derived9466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9466 := by
  apply localUnsat_implies_entails f9466 [c9419, c9347, c9443, c9455, c9462, c9215, c9465, c9256, c9257, c3630, c3653, c3633, c3664, c4043, c2886, c3652, c4258, c5009] c9466 unsat9466 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9443 := derived9443 a h
  have h3 : Entails.eval a c9455 := derived9455 a h
  have h4 : Entails.eval a c9462 := derived9462 a h
  have h5 : Entails.eval a c9215 := derived9215 a h
  have h6 : Entails.eval a c9465 := derived9465 a h
  have h7 : Entails.eval a c9256 := derived9256 a h
  have h8 : Entails.eval a c9257 := derived9257 a h
  have h9 : Entails.eval a c3630 := h 3629 (by decide)
  have h10 : Entails.eval a c3653 := h 3652 (by decide)
  have h11 : Entails.eval a c3633 := h 3632 (by decide)
  have h12 : Entails.eval a c3664 := h 3663 (by decide)
  have h13 : Entails.eval a c4043 := h 4042 (by decide)
  have h14 : Entails.eval a c2886 := h 2885 (by decide)
  have h15 : Entails.eval a c3652 := h 3651 (by decide)
  have h16 : Entails.eval a c4258 := h 4257 (by decide)
  have h17 : Entails.eval a c5009 := h 5008 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9467 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨64, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c1424, some c1425, some c1451, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9467 : lratChecker f9467 p9467 = .success := by decide +kernel
theorem unsat9467 : Unsatisfiable (PosFin 65) f9467 := by
  apply lratCheckerSound f9467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9467
  · intro a ha; simp [p9467] at ha; subst a; trivial
  · exact checked9467
theorem derived9467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9467 := by
  apply localUnsat_implies_entails f9467 [c8269, c7994, c1424, c1425, c1451] c9467 unsat9467 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c1424 := h 1423 (by decide)
  have h3 : Entails.eval a c1425 := h 1424 (by decide)
  have h4 : Entails.eval a c1451 := h 1450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9468 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9419, some c9347, some c9466, some c7994, some c8269, some c8383, some c9467, some c9416, some c1367, some c1366, some c1394, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9468 : lratChecker f9468 p9468 = .success := by decide +kernel
theorem unsat9468 : Unsatisfiable (PosFin 65) f9468 := by
  apply lratCheckerSound f9468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9468
  · intro a ha; simp [p9468] at ha; subst a; trivial
  · exact checked9468
theorem derived9468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9468 := by
  apply localUnsat_implies_entails f9468 [c9419, c9347, c9466, c7994, c8269, c8383, c9467, c9416, c1367, c1366, c1394] c9468 unsat9468 (by rfl) a
  have h0 : Entails.eval a c9419 := derived9419 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9466 := derived9466 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c8383 := derived8383 a h
  have h6 : Entails.eval a c9467 := derived9467 a h
  have h7 : Entails.eval a c9416 := derived9416 a h
  have h8 : Entails.eval a c1367 := h 1366 (by decide)
  have h9 : Entails.eval a c1366 := h 1365 (by decide)
  have h10 : Entails.eval a c1394 := h 1393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9469 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9217, some c9382, some c3718, some c3732, some c8007, some c2436, some c3726, some c2425, some c2444, some c2999, some c2439, some c9377, some c2396, some c3712, some c2394, some c2978, some c2995, some c2379, some c2390, some c2988, some c2403, some c2381, some c2382, some c2413, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked9469 : lratChecker f9469 p9469 = .success := by decide +kernel
theorem unsat9469 : Unsatisfiable (PosFin 65) f9469 := by
  apply lratCheckerSound f9469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9469
  · intro a ha; simp [p9469] at ha; subst a; trivial
  · exact checked9469
theorem derived9469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9469 := by
  apply localUnsat_implies_entails f9469 [c9217, c9382, c3718, c3732, c8007, c2436, c3726, c2425, c2444, c2999, c2439, c9377, c2396, c3712, c2394, c2978, c2995, c2379, c2390, c2988, c2403, c2381, c2382, c2413] c9469 unsat9469 (by rfl) a
  have h0 : Entails.eval a c9217 := derived9217 a h
  have h1 : Entails.eval a c9382 := derived9382 a h
  have h2 : Entails.eval a c3718 := h 3717 (by decide)
  have h3 : Entails.eval a c3732 := h 3731 (by decide)
  have h4 : Entails.eval a c8007 := derived8007 a h
  have h5 : Entails.eval a c2436 := h 2435 (by decide)
  have h6 : Entails.eval a c3726 := h 3725 (by decide)
  have h7 : Entails.eval a c2425 := h 2424 (by decide)
  have h8 : Entails.eval a c2444 := h 2443 (by decide)
  have h9 : Entails.eval a c2999 := h 2998 (by decide)
  have h10 : Entails.eval a c2439 := h 2438 (by decide)
  have h11 : Entails.eval a c9377 := derived9377 a h
  have h12 : Entails.eval a c2396 := h 2395 (by decide)
  have h13 : Entails.eval a c3712 := h 3711 (by decide)
  have h14 : Entails.eval a c2394 := h 2393 (by decide)
  have h15 : Entails.eval a c2978 := h 2977 (by decide)
  have h16 : Entails.eval a c2995 := h 2994 (by decide)
  have h17 : Entails.eval a c2379 := h 2378 (by decide)
  have h18 : Entails.eval a c2390 := h 2389 (by decide)
  have h19 : Entails.eval a c2988 := h 2987 (by decide)
  have h20 : Entails.eval a c2403 := h 2402 (by decide)
  have h21 : Entails.eval a c2381 := h 2380 (by decide)
  have h22 : Entails.eval a c2382 := h 2381 (by decide)
  have h23 : Entails.eval a c2413 := h 2412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9470 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3695, some c3698, some c2972, some c2979, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9470 : lratChecker f9470 p9470 = .success := by decide +kernel
theorem unsat9470 : Unsatisfiable (PosFin 65) f9470 := by
  apply lratCheckerSound f9470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9470
  · intro a ha; simp [p9470] at ha; subst a; trivial
  · exact checked9470
theorem derived9470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9470 := by
  apply localUnsat_implies_entails f9470 [c3695, c3698, c2972, c2979] c9470 unsat9470 (by rfl) a
  have h0 : Entails.eval a c3695 := h 3694 (by decide)
  have h1 : Entails.eval a c3698 := h 3697 (by decide)
  have h2 : Entails.eval a c2972 := h 2971 (by decide)
  have h3 : Entails.eval a c2979 := h 2978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9471 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9217, some c9382, some c3718, some c3732, some c2436, some c8007, some c3726, some c2425, some c2444, some c9469, some c9470, some c2984, some c3707, some c3706, some c2993, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9471 : lratChecker f9471 p9471 = .success := by decide +kernel
theorem unsat9471 : Unsatisfiable (PosFin 65) f9471 := by
  apply lratCheckerSound f9471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9471
  · intro a ha; simp [p9471] at ha; subst a; trivial
  · exact checked9471
theorem derived9471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9471 := by
  apply localUnsat_implies_entails f9471 [c9217, c9382, c3718, c3732, c2436, c8007, c3726, c2425, c2444, c9469, c9470, c2984, c3707, c3706, c2993] c9471 unsat9471 (by rfl) a
  have h0 : Entails.eval a c9217 := derived9217 a h
  have h1 : Entails.eval a c9382 := derived9382 a h
  have h2 : Entails.eval a c3718 := h 3717 (by decide)
  have h3 : Entails.eval a c3732 := h 3731 (by decide)
  have h4 : Entails.eval a c2436 := h 2435 (by decide)
  have h5 : Entails.eval a c8007 := derived8007 a h
  have h6 : Entails.eval a c3726 := h 3725 (by decide)
  have h7 : Entails.eval a c2425 := h 2424 (by decide)
  have h8 : Entails.eval a c2444 := h 2443 (by decide)
  have h9 : Entails.eval a c9469 := derived9469 a h
  have h10 : Entails.eval a c9470 := derived9470 a h
  have h11 : Entails.eval a c2984 := h 2983 (by decide)
  have h12 : Entails.eval a c3707 := h 3706 (by decide)
  have h13 : Entails.eval a c3706 := h 3705 (by decide)
  have h14 : Entails.eval a c2993 := h 2992 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9472 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9471, some c7994, some c8269, some c3728, some c2445, some c2444, some c2420, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9472 : lratChecker f9472 p9472 = .success := by decide +kernel
theorem unsat9472 : Unsatisfiable (PosFin 65) f9472 := by
  apply lratCheckerSound f9472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9472
  · intro a ha; simp [p9472] at ha; subst a; trivial
  · exact checked9472
theorem derived9472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9472 := by
  apply localUnsat_implies_entails f9472 [c9471, c7994, c8269, c3728, c2445, c2444, c2420] c9472 unsat9472 (by rfl) a
  have h0 : Entails.eval a c9471 := derived9471 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c3728 := h 3727 (by decide)
  have h4 : Entails.eval a c2445 := h 2444 (by decide)
  have h5 : Entails.eval a c2444 := h 2443 (by decide)
  have h6 : Entails.eval a c2420 := h 2419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9473 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9419, some c9468, some c9472, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9473 : lratChecker f9473 p9473 = .success := by decide +kernel
theorem unsat9473 : Unsatisfiable (PosFin 65) f9473 := by
  apply lratCheckerSound f9473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9473
  · intro a ha; simp [p9473] at ha; subst a; trivial
  · exact checked9473
theorem derived9473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9473 := by
  apply localUnsat_implies_entails f9473 [c9347, c9419, c9468, c9472] c9473 unsat9473 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9419 := derived9419 a h
  have h2 : Entails.eval a c9468 := derived9468 a h
  have h3 : Entails.eval a c9472 := derived9472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9474 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4614, some c4613, some c4616, some c4636, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p9474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9474 : lratChecker f9474 p9474 = .success := by decide +kernel
theorem unsat9474 : Unsatisfiable (PosFin 65) f9474 := by
  apply lratCheckerSound f9474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9474
  · intro a ha; simp [p9474] at ha; subst a; trivial
  · exact checked9474
theorem derived9474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9474 := by
  apply localUnsat_implies_entails f9474 [c4614, c4613, c4616, c4636] c9474 unsat9474 (by rfl) a
  have h0 : Entails.eval a c4614 := h 4613 (by decide)
  have h1 : Entails.eval a c4613 := h 4612 (by decide)
  have h2 : Entails.eval a c4616 := h 4615 (by decide)
  have h3 : Entails.eval a c4636 := h 4635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9475 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9347, some c9129, some c2840, some c3581, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9475 : lratChecker f9475 p9475 = .success := by decide +kernel
theorem unsat9475 : Unsatisfiable (PosFin 65) f9475 := by
  apply lratCheckerSound f9475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9475
  · intro a ha; simp [p9475] at ha; subst a; trivial
  · exact checked9475
theorem derived9475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9475 := by
  apply localUnsat_implies_entails f9475 [c8269, c9347, c9129, c2840, c3581] c9475 unsat9475 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9129 := derived9129 a h
  have h3 : Entails.eval a c2840 := h 2839 (by decide)
  have h4 : Entails.eval a c3581 := h 3580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9476 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3582, some c3586, some c3593, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9476 : lratChecker f9476 p9476 = .success := by decide +kernel
theorem unsat9476 : Unsatisfiable (PosFin 65) f9476 := by
  apply lratCheckerSound f9476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9476
  · intro a ha; simp [p9476] at ha; subst a; trivial
  · exact checked9476
theorem derived9476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9476 := by
  apply localUnsat_implies_entails f9476 [c3582, c3586, c3593] c9476 unsat9476 (by rfl) a
  have h0 : Entails.eval a c3582 := h 3581 (by decide)
  have h1 : Entails.eval a c3586 := h 3585 (by decide)
  have h2 : Entails.eval a c3593 := h 3592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9477 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2845, some c2862, some c2863, some c2848, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p9477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9477 : lratChecker f9477 p9477 = .success := by decide +kernel
theorem unsat9477 : Unsatisfiable (PosFin 65) f9477 := by
  apply lratCheckerSound f9477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9477
  · intro a ha; simp [p9477] at ha; subst a; trivial
  · exact checked9477
theorem derived9477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9477 := by
  apply localUnsat_implies_entails f9477 [c2845, c2862, c2863, c2848] c9477 unsat9477 (by rfl) a
  have h0 : Entails.eval a c2845 := h 2844 (by decide)
  have h1 : Entails.eval a c2862 := h 2861 (by decide)
  have h2 : Entails.eval a c2863 := h 2862 (by decide)
  have h3 : Entails.eval a c2848 := h 2847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9478 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9445, some c9477, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9478 : lratChecker f9478 p9478 = .success := by decide +kernel
theorem unsat9478 : Unsatisfiable (PosFin 65) f9478 := by
  apply lratCheckerSound f9478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9478
  · intro a ha; simp [p9478] at ha; subst a; trivial
  · exact checked9478
theorem derived9478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9478 := by
  apply localUnsat_implies_entails f9478 [c9347, c9445, c9477] c9478 unsat9478 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9445 := derived9445 a h
  have h2 : Entails.eval a c9477 := derived9477 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9479 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c9405, some c1427, some c9395, some c1227, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9479 : lratChecker f9479 p9479 = .success := by decide +kernel
theorem unsat9479 : Unsatisfiable (PosFin 65) f9479 := by
  apply lratCheckerSound f9479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9479
  · intro a ha; simp [p9479] at ha; subst a; trivial
  · exact checked9479
theorem derived9479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9479 := by
  apply localUnsat_implies_entails f9479 [c8269, c9405, c1427, c9395, c1227] c9479 unsat9479 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c9405 := derived9405 a h
  have h2 : Entails.eval a c1427 := h 1426 (by decide)
  have h3 : Entails.eval a c9395 := derived9395 a h
  have h4 : Entails.eval a c1227 := h 1226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9480 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9473, some c9347, some c8269, some c9474, some c9475, some c9476, some c9478, some c9479, some c2842, some c2841, some c2843, some c2867, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9480 : lratChecker f9480 p9480 = .success := by decide +kernel
theorem unsat9480 : Unsatisfiable (PosFin 65) f9480 := by
  apply lratCheckerSound f9480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9480
  · intro a ha; simp [p9480] at ha; subst a; trivial
  · exact checked9480
theorem derived9480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9480 := by
  apply localUnsat_implies_entails f9480 [c9473, c9347, c8269, c9474, c9475, c9476, c9478, c9479, c2842, c2841, c2843, c2867] c9480 unsat9480 (by rfl) a
  have h0 : Entails.eval a c9473 := derived9473 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c9474 := derived9474 a h
  have h4 : Entails.eval a c9475 := derived9475 a h
  have h5 : Entails.eval a c9476 := derived9476 a h
  have h6 : Entails.eval a c9478 := derived9478 a h
  have h7 : Entails.eval a c9479 := derived9479 a h
  have h8 : Entails.eval a c2842 := h 2841 (by decide)
  have h9 : Entails.eval a c2841 := h 2840 (by decide)
  have h10 : Entails.eval a c2843 := h 2842 (by decide)
  have h11 : Entails.eval a c2867 := h 2866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9481 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨7, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3581, some c3149, some c2840, some c2912, some c3807, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9481 : lratChecker f9481 p9481 = .success := by decide +kernel
theorem unsat9481 : Unsatisfiable (PosFin 65) f9481 := by
  apply lratCheckerSound f9481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9481
  · intro a ha; simp [p9481] at ha; subst a; trivial
  · exact checked9481
theorem derived9481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9481 := by
  apply localUnsat_implies_entails f9481 [c3581, c3149, c2840, c2912, c3807] c9481 unsat9481 (by rfl) a
  have h0 : Entails.eval a c3581 := h 3580 (by decide)
  have h1 : Entails.eval a c3149 := h 3148 (by decide)
  have h2 : Entails.eval a c2840 := h 2839 (by decide)
  have h3 : Entails.eval a c2912 := h 2911 (by decide)
  have h4 : Entails.eval a c3807 := h 3806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9482 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1430, some c1436, some c1438, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9482 : lratChecker f9482 p9482 = .success := by decide +kernel
theorem unsat9482 : Unsatisfiable (PosFin 65) f9482 := by
  apply lratCheckerSound f9482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9482
  · intro a ha; simp [p9482] at ha; subst a; trivial
  · exact checked9482
theorem derived9482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9482 := by
  apply localUnsat_implies_entails f9482 [c1430, c1436, c1438] c9482 unsat9482 (by rfl) a
  have h0 : Entails.eval a c1430 := h 1429 (by decide)
  have h1 : Entails.eval a c1436 := h 1435 (by decide)
  have h2 : Entails.eval a c1438 := h 1437 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9483 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9483 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c1214, some c1228, some c2604, some c3041, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9483 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9483 : lratChecker f9483 p9483 = .success := by decide +kernel
theorem unsat9483 : Unsatisfiable (PosFin 65) f9483 := by
  apply lratCheckerSound f9483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9483
  · intro a ha; simp [p9483] at ha; subst a; trivial
  · exact checked9483
theorem derived9483 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9483 := by
  apply localUnsat_implies_entails f9483 [c9347, c1214, c1228, c2604, c3041] c9483 unsat9483 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c1214 := h 1213 (by decide)
  have h2 : Entails.eval a c1228 := h 1227 (by decide)
  have h3 : Entails.eval a c2604 := h 2603 (by decide)
  have h4 : Entails.eval a c3041 := h 3040 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9484 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9484 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9478, some c9389, some c8659, some c9483, some c3040, some c3402, some c4182, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9484 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9484 : lratChecker f9484 p9484 = .success := by decide +kernel
theorem unsat9484 : Unsatisfiable (PosFin 65) f9484 := by
  apply lratCheckerSound f9484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9484
  · intro a ha; simp [p9484] at ha; subst a; trivial
  · exact checked9484
theorem derived9484 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9484 := by
  apply localUnsat_implies_entails f9484 [c9478, c9389, c8659, c9483, c3040, c3402, c4182] c9484 unsat9484 (by rfl) a
  have h0 : Entails.eval a c9478 := derived9478 a h
  have h1 : Entails.eval a c9389 := derived9389 a h
  have h2 : Entails.eval a c8659 := derived8659 a h
  have h3 : Entails.eval a c9483 := derived9483 a h
  have h4 : Entails.eval a c3040 := h 3039 (by decide)
  have h5 : Entails.eval a c3402 := h 3401 (by decide)
  have h6 : Entails.eval a c4182 := h 4181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9485 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9485 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9480, some c9473, some c9347, some c9474, some c9481, some c9476, some c9478, some c9484, some c2842, some c2841, some c2843, some c2867, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9485 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9485 : lratChecker f9485 p9485 = .success := by decide +kernel
theorem unsat9485 : Unsatisfiable (PosFin 65) f9485 := by
  apply lratCheckerSound f9485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9485
  · intro a ha; simp [p9485] at ha; subst a; trivial
  · exact checked9485
theorem derived9485 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9485 := by
  apply localUnsat_implies_entails f9485 [c9480, c9473, c9347, c9474, c9481, c9476, c9478, c9484, c2842, c2841, c2843, c2867] c9485 unsat9485 (by rfl) a
  have h0 : Entails.eval a c9480 := derived9480 a h
  have h1 : Entails.eval a c9473 := derived9473 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9474 := derived9474 a h
  have h4 : Entails.eval a c9481 := derived9481 a h
  have h5 : Entails.eval a c9476 := derived9476 a h
  have h6 : Entails.eval a c9478 := derived9478 a h
  have h7 : Entails.eval a c9484 := derived9484 a h
  have h8 : Entails.eval a c2842 := h 2841 (by decide)
  have h9 : Entails.eval a c2841 := h 2840 (by decide)
  have h10 : Entails.eval a c2843 := h 2842 (by decide)
  have h11 : Entails.eval a c2867 := h 2866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9486 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9486 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c4623, some c2676, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9486 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9486 : lratChecker f9486 p9486 = .success := by decide +kernel
theorem unsat9486 : Unsatisfiable (PosFin 65) f9486 := by
  apply lratCheckerSound f9486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9486
  · intro a ha; simp [p9486] at ha; subst a; trivial
  · exact checked9486
theorem derived9486 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9486 := by
  apply localUnsat_implies_entails f9486 [c7994, c4623, c2676] c9486 unsat9486 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c4623 := h 4622 (by decide)
  have h2 : Entails.eval a c2676 := h 2675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9487 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨63, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9487 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3148, some c2877, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9487 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9487 : lratChecker f9487 p9487 = .success := by decide +kernel
theorem unsat9487 : Unsatisfiable (PosFin 65) f9487 := by
  apply lratCheckerSound f9487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9487
  · intro a ha; simp [p9487] at ha; subst a; trivial
  · exact checked9487
theorem derived9487 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9487 := by
  apply localUnsat_implies_entails f9487 [c3148, c2877] c9487 unsat9487 (by rfl) a
  have h0 : Entails.eval a c3148 := h 3147 (by decide)
  have h1 : Entails.eval a c2877 := h 2876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9488 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨64, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9488 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c1366, some c3583, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9488 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9488 : lratChecker f9488 p9488 = .success := by decide +kernel
theorem unsat9488 : Unsatisfiable (PosFin 65) f9488 := by
  apply lratCheckerSound f9488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9488
  · intro a ha; simp [p9488] at ha; subst a; trivial
  · exact checked9488
theorem derived9488 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9488 := by
  apply localUnsat_implies_entails f9488 [c7994, c1366, c3583] c9488 unsat9488 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c1366 := h 1365 (by decide)
  have h2 : Entails.eval a c3583 := h 3582 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9489 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9489 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9473, some c9347, some c9480, some c9485, some c7994, some c9467, some c9486, some c9487, some c9488, some c9478, some c2843, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9489 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9489 : lratChecker f9489 p9489 = .success := by decide +kernel
theorem unsat9489 : Unsatisfiable (PosFin 65) f9489 := by
  apply lratCheckerSound f9489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9489
  · intro a ha; simp [p9489] at ha; subst a; trivial
  · exact checked9489
theorem derived9489 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9489 := by
  apply localUnsat_implies_entails f9489 [c9473, c9347, c9480, c9485, c7994, c9467, c9486, c9487, c9488, c9478, c2843] c9489 unsat9489 (by rfl) a
  have h0 : Entails.eval a c9473 := derived9473 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9480 := derived9480 a h
  have h3 : Entails.eval a c9485 := derived9485 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c9467 := derived9467 a h
  have h6 : Entails.eval a c9486 := derived9486 a h
  have h7 : Entails.eval a c9487 := derived9487 a h
  have h8 : Entails.eval a c9488 := derived9488 a h
  have h9 : Entails.eval a c9478 := derived9478 a h
  have h10 : Entails.eval a c2843 := h 2842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9490 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9490 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9293, some c9474, some c9476, some c2475, some c2472, some c9222, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9490 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9490 : lratChecker f9490 p9490 = .success := by decide +kernel
theorem unsat9490 : Unsatisfiable (PosFin 65) f9490 := by
  apply lratCheckerSound f9490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9490
  · intro a ha; simp [p9490] at ha; subst a; trivial
  · exact checked9490
theorem derived9490 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9490 := by
  apply localUnsat_implies_entails f9490 [c9293, c9474, c9476, c2475, c2472, c9222] c9490 unsat9490 (by rfl) a
  have h0 : Entails.eval a c9293 := derived9293 a h
  have h1 : Entails.eval a c9474 := derived9474 a h
  have h2 : Entails.eval a c9476 := derived9476 a h
  have h3 : Entails.eval a c2475 := h 2474 (by decide)
  have h4 : Entails.eval a c2472 := h 2471 (by decide)
  have h5 : Entails.eval a c9222 := derived9222 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9491 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9491 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9473, some c9347, some c9489, some c9490, some c7994, some c8269, some c8383, some c9467, some c9309, some c9304, some c9048, some c9416, some c3793, some c4419, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9491 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9491 : lratChecker f9491 p9491 = .success := by decide +kernel
theorem unsat9491 : Unsatisfiable (PosFin 65) f9491 := by
  apply lratCheckerSound f9491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9491
  · intro a ha; simp [p9491] at ha; subst a; trivial
  · exact checked9491
theorem derived9491 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9491 := by
  apply localUnsat_implies_entails f9491 [c9473, c9347, c9489, c9490, c7994, c8269, c8383, c9467, c9309, c9304, c9048, c9416, c3793, c4419] c9491 unsat9491 (by rfl) a
  have h0 : Entails.eval a c9473 := derived9473 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9489 := derived9489 a h
  have h3 : Entails.eval a c9490 := derived9490 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c8383 := derived8383 a h
  have h7 : Entails.eval a c9467 := derived9467 a h
  have h8 : Entails.eval a c9309 := derived9309 a h
  have h9 : Entails.eval a c9304 := derived9304 a h
  have h10 : Entails.eval a c9048 := derived9048 a h
  have h11 : Entails.eval a c9416 := derived9416 a h
  have h12 : Entails.eval a c3793 := h 3792 (by decide)
  have h13 : Entails.eval a c4419 := h 4418 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9492 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9492 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3721, some c3723, some c3720, some c3738, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9492 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9492 : lratChecker f9492 p9492 = .success := by decide +kernel
theorem unsat9492 : Unsatisfiable (PosFin 65) f9492 := by
  apply lratCheckerSound f9492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9492
  · intro a ha; simp [p9492] at ha; subst a; trivial
  · exact checked9492
theorem derived9492 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9492 := by
  apply localUnsat_implies_entails f9492 [c3721, c3723, c3720, c3738] c9492 unsat9492 (by rfl) a
  have h0 : Entails.eval a c3721 := h 3720 (by decide)
  have h1 : Entails.eval a c3723 := h 3722 (by decide)
  have h2 : Entails.eval a c3720 := h 3719 (by decide)
  have h3 : Entails.eval a c3738 := h 3737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9493 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9493 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9492, some c8269, some c9189, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9493 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9493 : lratChecker f9493 p9493 = .success := by decide +kernel
theorem unsat9493 : Unsatisfiable (PosFin 65) f9493 := by
  apply lratCheckerSound f9493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9493
  · intro a ha; simp [p9493] at ha; subst a; trivial
  · exact checked9493
theorem derived9493 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9493 := by
  apply localUnsat_implies_entails f9493 [c9492, c8269, c9189] c9493 unsat9493 (by rfl) a
  have h0 : Entails.eval a c9492 := derived9492 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9189 := derived9189 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9494 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9494 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9473, some c9491, some c9493, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9494 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9494 : lratChecker f9494 p9494 = .success := by decide +kernel
theorem unsat9494 : Unsatisfiable (PosFin 65) f9494 := by
  apply lratCheckerSound f9494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9494
  · intro a ha; simp [p9494] at ha; subst a; trivial
  · exact checked9494
theorem derived9494 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9494 := by
  apply localUnsat_implies_entails f9494 [c9473, c9491, c9493] c9494 unsat9494 (by rfl) a
  have h0 : Entails.eval a c9473 := derived9473 a h
  have h1 : Entails.eval a c9491 := derived9491 a h
  have h2 : Entails.eval a c9493 := derived9493 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9495 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9495 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1292, some c1267, some c1269, some c1281, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9495 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9495 : lratChecker f9495 p9495 = .success := by decide +kernel
theorem unsat9495 : Unsatisfiable (PosFin 65) f9495 := by
  apply lratCheckerSound f9495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9495
  · intro a ha; simp [p9495] at ha; subst a; trivial
  · exact checked9495
theorem derived9495 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9495 := by
  apply localUnsat_implies_entails f9495 [c1292, c1267, c1269, c1281] c9495 unsat9495 (by rfl) a
  have h0 : Entails.eval a c1292 := h 1291 (by decide)
  have h1 : Entails.eval a c1267 := h 1266 (by decide)
  have h2 : Entails.eval a c1269 := h 1268 (by decide)
  have h3 : Entails.eval a c1281 := h 1280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9496 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9496 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9445, some c9479, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9496 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9496 : lratChecker f9496 p9496 = .success := by decide +kernel
theorem unsat9496 : Unsatisfiable (PosFin 65) f9496 := by
  apply lratCheckerSound f9496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9496
  · intro a ha; simp [p9496] at ha; subst a; trivial
  · exact checked9496
theorem derived9496 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9496 := by
  apply localUnsat_implies_entails f9496 [c9445, c9479] c9496 unsat9496 (by rfl) a
  have h0 : Entails.eval a c9445 := derived9445 a h
  have h1 : Entails.eval a c9479 := derived9479 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9497 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9497 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1278, some c1277, some c1293, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9497 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9497 : lratChecker f9497 p9497 = .success := by decide +kernel
theorem unsat9497 : Unsatisfiable (PosFin 65) f9497 := by
  apply lratCheckerSound f9497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9497
  · intro a ha; simp [p9497] at ha; subst a; trivial
  · exact checked9497
theorem derived9497 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9497 := by
  apply localUnsat_implies_entails f9497 [c1278, c1277, c1293] c9497 unsat9497 (by rfl) a
  have h0 : Entails.eval a c1278 := h 1277 (by decide)
  have h1 : Entails.eval a c1277 := h 1276 (by decide)
  have h2 : Entails.eval a c1293 := h 1292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9498 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9498 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9495, some c9496, some c9497, some c1288, some c1290, some c9477, some c1372, some c2173, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9498 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9498 : lratChecker f9498 p9498 = .success := by decide +kernel
theorem unsat9498 : Unsatisfiable (PosFin 65) f9498 := by
  apply lratCheckerSound f9498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9498
  · intro a ha; simp [p9498] at ha; subst a; trivial
  · exact checked9498
theorem derived9498 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9498 := by
  apply localUnsat_implies_entails f9498 [c9347, c9495, c9496, c9497, c1288, c1290, c9477, c1372, c2173] c9498 unsat9498 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9495 := derived9495 a h
  have h2 : Entails.eval a c9496 := derived9496 a h
  have h3 : Entails.eval a c9497 := derived9497 a h
  have h4 : Entails.eval a c1288 := h 1287 (by decide)
  have h5 : Entails.eval a c1290 := h 1289 (by decide)
  have h6 : Entails.eval a c9477 := derived9477 a h
  have h7 : Entails.eval a c1372 := h 1371 (by decide)
  have h8 : Entails.eval a c2173 := h 2172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9499 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9499 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9389, some c3039, some c2577, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9499 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9499 : lratChecker f9499 p9499 = .success := by decide +kernel
theorem unsat9499 : Unsatisfiable (PosFin 65) f9499 := by
  apply lratCheckerSound f9499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9499
  · intro a ha; simp [p9499] at ha; subst a; trivial
  · exact checked9499
theorem derived9499 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9499 := by
  apply localUnsat_implies_entails f9499 [c9347, c9389, c3039, c2577] c9499 unsat9499 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9389 := derived9389 a h
  have h2 : Entails.eval a c3039 := h 3038 (by decide)
  have h3 : Entails.eval a c2577 := h 2576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9500 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨58, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9500 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9456, some c2673, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9500 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9500 : lratChecker f9500 p9500 = .success := by decide +kernel
theorem unsat9500 : Unsatisfiable (PosFin 65) f9500 := by
  apply lratCheckerSound f9500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9500
  · intro a ha; simp [p9500] at ha; subst a; trivial
  · exact checked9500
theorem derived9500 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9500 := by
  apply localUnsat_implies_entails f9500 [c9456, c2673] c9500 unsat9500 (by rfl) a
  have h0 : Entails.eval a c9456 := derived9456 a h
  have h1 : Entails.eval a c2673 := h 2672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9501 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9501 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9499, some c9500, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9501 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9501 : lratChecker f9501 p9501 = .success := by decide +kernel
theorem unsat9501 : Unsatisfiable (PosFin 65) f9501 := by
  apply lratCheckerSound f9501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9501
  · intro a ha; simp [p9501] at ha; subst a; trivial
  · exact checked9501
theorem derived9501 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9501 := by
  apply localUnsat_implies_entails f9501 [c9347, c9499, c9500] c9501 unsat9501 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9499 := derived9499 a h
  have h2 : Entails.eval a c9500 := derived9500 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9502 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9502 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1292, some c9498, some c9347, some c9389, some c1444, some c3418, some c3806, some c2914, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9502 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9502 : lratChecker f9502 p9502 = .success := by decide +kernel
theorem unsat9502 : Unsatisfiable (PosFin 65) f9502 := by
  apply lratCheckerSound f9502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9502
  · intro a ha; simp [p9502] at ha; subst a; trivial
  · exact checked9502
theorem derived9502 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9502 := by
  apply localUnsat_implies_entails f9502 [c1292, c9498, c9347, c9389, c1444, c3418, c3806, c2914] c9502 unsat9502 (by rfl) a
  have h0 : Entails.eval a c1292 := h 1291 (by decide)
  have h1 : Entails.eval a c9498 := derived9498 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9389 := derived9389 a h
  have h4 : Entails.eval a c1444 := h 1443 (by decide)
  have h5 : Entails.eval a c3418 := h 3417 (by decide)
  have h6 : Entails.eval a c3806 := h 3805 (by decide)
  have h7 : Entails.eval a c2914 := h 2913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9503 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9503 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1384, some c3578, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9503 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9503 : lratChecker f9503 p9503 = .success := by decide +kernel
theorem unsat9503 : Unsatisfiable (PosFin 65) f9503 := by
  apply lratCheckerSound f9503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9503
  · intro a ha; simp [p9503] at ha; subst a; trivial
  · exact checked9503
theorem derived9503 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9503 := by
  apply localUnsat_implies_entails f9503 [c1384, c3578] c9503 unsat9503 (by rfl) a
  have h0 : Entails.eval a c1384 := h 1383 (by decide)
  have h1 : Entails.eval a c3578 := h 3577 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9504 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9504 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9498, some c9347, some c1292, some c9501, some c9502, some c9503, some c9356, some c3418, some c2876, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9504 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9504 : lratChecker f9504 p9504 = .success := by decide +kernel
theorem unsat9504 : Unsatisfiable (PosFin 65) f9504 := by
  apply lratCheckerSound f9504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9504
  · intro a ha; simp [p9504] at ha; subst a; trivial
  · exact checked9504
theorem derived9504 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9504 := by
  apply localUnsat_implies_entails f9504 [c9498, c9347, c1292, c9501, c9502, c9503, c9356, c3418, c2876] c9504 unsat9504 (by rfl) a
  have h0 : Entails.eval a c9498 := derived9498 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c1292 := h 1291 (by decide)
  have h3 : Entails.eval a c9501 := derived9501 a h
  have h4 : Entails.eval a c9502 := derived9502 a h
  have h5 : Entails.eval a c9503 := derived9503 a h
  have h6 : Entails.eval a c9356 := derived9356 a h
  have h7 : Entails.eval a c3418 := h 3417 (by decide)
  have h8 : Entails.eval a c2876 := h 2875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9505 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9505 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9389, some c9367, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9505 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9505 : lratChecker f9505 p9505 = .success := by decide +kernel
theorem unsat9505 : Unsatisfiable (PosFin 65) f9505 := by
  apply lratCheckerSound f9505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9505
  · intro a ha; simp [p9505] at ha; subst a; trivial
  · exact checked9505
theorem derived9505 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9505 := by
  apply localUnsat_implies_entails f9505 [c9389, c9367] c9505 unsat9505 (by rfl) a
  have h0 : Entails.eval a c9389 := derived9389 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9506 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9506 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9504, some c9498, some c9347, some c9501, some c9505, some c2682, some c9115, some c2681, some c2672, some c2693, some c1272, some c1284, some c9195, some c8496, some c8580, some c2658, some c2666, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9506 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9506 : lratChecker f9506 p9506 = .success := by decide +kernel
theorem unsat9506 : Unsatisfiable (PosFin 65) f9506 := by
  apply lratCheckerSound f9506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9506
  · intro a ha; simp [p9506] at ha; subst a; trivial
  · exact checked9506
theorem derived9506 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9506 := by
  apply localUnsat_implies_entails f9506 [c9504, c9498, c9347, c9501, c9505, c2682, c9115, c2681, c2672, c2693, c1272, c1284, c9195, c8496, c8580, c2658, c2666] c9506 unsat9506 (by rfl) a
  have h0 : Entails.eval a c9504 := derived9504 a h
  have h1 : Entails.eval a c9498 := derived9498 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9501 := derived9501 a h
  have h4 : Entails.eval a c9505 := derived9505 a h
  have h5 : Entails.eval a c2682 := h 2681 (by decide)
  have h6 : Entails.eval a c9115 := derived9115 a h
  have h7 : Entails.eval a c2681 := h 2680 (by decide)
  have h8 : Entails.eval a c2672 := h 2671 (by decide)
  have h9 : Entails.eval a c2693 := h 2692 (by decide)
  have h10 : Entails.eval a c1272 := h 1271 (by decide)
  have h11 : Entails.eval a c1284 := h 1283 (by decide)
  have h12 : Entails.eval a c9195 := derived9195 a h
  have h13 : Entails.eval a c8496 := derived8496 a h
  have h14 : Entails.eval a c8580 := derived8580 a h
  have h15 : Entails.eval a c2658 := h 2657 (by decide)
  have h16 : Entails.eval a c2666 := h 2665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9507 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9507 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9504, some c9498, some c9347, some c9389, some c9505, some c9352, some c3418, some c4944, some c2910, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9507 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9507 : lratChecker f9507 p9507 = .success := by decide +kernel
theorem unsat9507 : Unsatisfiable (PosFin 65) f9507 := by
  apply lratCheckerSound f9507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9507
  · intro a ha; simp [p9507] at ha; subst a; trivial
  · exact checked9507
theorem derived9507 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9507 := by
  apply localUnsat_implies_entails f9507 [c9494, c9504, c9498, c9347, c9389, c9505, c9352, c3418, c4944, c2910] c9507 unsat9507 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9504 := derived9504 a h
  have h2 : Entails.eval a c9498 := derived9498 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9389 := derived9389 a h
  have h5 : Entails.eval a c9505 := derived9505 a h
  have h6 : Entails.eval a c9352 := derived9352 a h
  have h7 : Entails.eval a c3418 := h 3417 (by decide)
  have h8 : Entails.eval a c4944 := h 4943 (by decide)
  have h9 : Entails.eval a c2910 := h 2909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9508 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9508 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3418, some c2876, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9508 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9508 : lratChecker f9508 p9508 = .success := by decide +kernel
theorem unsat9508 : Unsatisfiable (PosFin 65) f9508 := by
  apply lratCheckerSound f9508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9508
  · intro a ha; simp [p9508] at ha; subst a; trivial
  · exact checked9508
theorem derived9508 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9508 := by
  apply localUnsat_implies_entails f9508 [c3418, c2876] c9508 unsat9508 (by rfl) a
  have h0 : Entails.eval a c3418 := h 3417 (by decide)
  have h1 : Entails.eval a c2876 := h 2875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9509 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9509 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9498, some c9347, some c8420, some c9463, some c9416, some c1280, some c1272, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9509 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9509 : lratChecker f9509 p9509 = .success := by decide +kernel
theorem unsat9509 : Unsatisfiable (PosFin 65) f9509 := by
  apply lratCheckerSound f9509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9509
  · intro a ha; simp [p9509] at ha; subst a; trivial
  · exact checked9509
theorem derived9509 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9509 := by
  apply localUnsat_implies_entails f9509 [c9498, c9347, c8420, c9463, c9416, c1280, c1272] c9509 unsat9509 (by rfl) a
  have h0 : Entails.eval a c9498 := derived9498 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c8420 := derived8420 a h
  have h3 : Entails.eval a c9463 := derived9463 a h
  have h4 : Entails.eval a c9416 := derived9416 a h
  have h5 : Entails.eval a c1280 := h 1279 (by decide)
  have h6 : Entails.eval a c1272 := h 1271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9510 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9510 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9347, some c9498, some c9504, some c9506, some c9507, some c9509, some c9508, some c9401, some c9115, some c9195, some c8496, some c8580, some c9403, some c2874, some c3414, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9510 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9510 : lratChecker f9510 p9510 = .success := by decide +kernel
theorem unsat9510 : Unsatisfiable (PosFin 65) f9510 := by
  apply lratCheckerSound f9510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9510
  · intro a ha; simp [p9510] at ha; subst a; trivial
  · exact checked9510
theorem derived9510 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9510 := by
  apply localUnsat_implies_entails f9510 [c9494, c9347, c9498, c9504, c9506, c9507, c9509, c9508, c9401, c9115, c9195, c8496, c8580, c9403, c2874, c3414] c9510 unsat9510 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9498 := derived9498 a h
  have h3 : Entails.eval a c9504 := derived9504 a h
  have h4 : Entails.eval a c9506 := derived9506 a h
  have h5 : Entails.eval a c9507 := derived9507 a h
  have h6 : Entails.eval a c9509 := derived9509 a h
  have h7 : Entails.eval a c9508 := derived9508 a h
  have h8 : Entails.eval a c9401 := derived9401 a h
  have h9 : Entails.eval a c9115 := derived9115 a h
  have h10 : Entails.eval a c9195 := derived9195 a h
  have h11 : Entails.eval a c8496 := derived8496 a h
  have h12 : Entails.eval a c8580 := derived8580 a h
  have h13 : Entails.eval a c9403 := derived9403 a h
  have h14 : Entails.eval a c2874 := h 2873 (by decide)
  have h15 : Entails.eval a c3414 := h 3413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9511 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9511 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9510, some c9322, some c9445, some c9482, some c8007, some c9452, some c9325, some c4955, some c3328, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9511 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9511 : lratChecker f9511 p9511 = .success := by decide +kernel
theorem unsat9511 : Unsatisfiable (PosFin 65) f9511 := by
  apply lratCheckerSound f9511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9511
  · intro a ha; simp [p9511] at ha; subst a; trivial
  · exact checked9511
theorem derived9511 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9511 := by
  apply localUnsat_implies_entails f9511 [c9494, c9510, c9322, c9445, c9482, c8007, c9452, c9325, c4955, c3328] c9511 unsat9511 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9510 := derived9510 a h
  have h2 : Entails.eval a c9322 := derived9322 a h
  have h3 : Entails.eval a c9445 := derived9445 a h
  have h4 : Entails.eval a c9482 := derived9482 a h
  have h5 : Entails.eval a c8007 := derived8007 a h
  have h6 : Entails.eval a c9452 := derived9452 a h
  have h7 : Entails.eval a c9325 := derived9325 a h
  have h8 : Entails.eval a c4955 := h 4954 (by decide)
  have h9 : Entails.eval a c3328 := h 3327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9512 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9512 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9500, some c9230, some c2682, some c9452, some c2681, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9512 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9512 : lratChecker f9512 p9512 = .success := by decide +kernel
theorem unsat9512 : Unsatisfiable (PosFin 65) f9512 := by
  apply lratCheckerSound f9512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9512
  · intro a ha; simp [p9512] at ha; subst a; trivial
  · exact checked9512
theorem derived9512 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9512 := by
  apply localUnsat_implies_entails f9512 [c9500, c9230, c2682, c9452, c2681] c9512 unsat9512 (by rfl) a
  have h0 : Entails.eval a c9500 := derived9500 a h
  have h1 : Entails.eval a c9230 := derived9230 a h
  have h2 : Entails.eval a c2682 := h 2681 (by decide)
  have h3 : Entails.eval a c9452 := derived9452 a h
  have h4 : Entails.eval a c2681 := h 2680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9513 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9513 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9324, some c9230, some c4944, some c2506, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9513 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9513 : lratChecker f9513 p9513 = .success := by decide +kernel
theorem unsat9513 : Unsatisfiable (PosFin 65) f9513 := by
  apply lratCheckerSound f9513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9513
  · intro a ha; simp [p9513] at ha; subst a; trivial
  · exact checked9513
theorem derived9513 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9513 := by
  apply localUnsat_implies_entails f9513 [c9324, c9230, c4944, c2506] c9513 unsat9513 (by rfl) a
  have h0 : Entails.eval a c9324 := derived9324 a h
  have h1 : Entails.eval a c9230 := derived9230 a h
  have h2 : Entails.eval a c4944 := h 4943 (by decide)
  have h3 : Entails.eval a c2506 := h 2505 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9514 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9514 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9510, some c9322, some c9347, some c9511, some c9512, some c9513, some c9463, some c3337, some c2164, some c4903, some c4951, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9514 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9514 : lratChecker f9514 p9514 = .success := by decide +kernel
theorem unsat9514 : Unsatisfiable (PosFin 65) f9514 := by
  apply lratCheckerSound f9514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9514
  · intro a ha; simp [p9514] at ha; subst a; trivial
  · exact checked9514
theorem derived9514 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9514 := by
  apply localUnsat_implies_entails f9514 [c9494, c9510, c9322, c9347, c9511, c9512, c9513, c9463, c3337, c2164, c4903, c4951] c9514 unsat9514 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9510 := derived9510 a h
  have h2 : Entails.eval a c9322 := derived9322 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9511 := derived9511 a h
  have h5 : Entails.eval a c9512 := derived9512 a h
  have h6 : Entails.eval a c9513 := derived9513 a h
  have h7 : Entails.eval a c9463 := derived9463 a h
  have h8 : Entails.eval a c3337 := h 3336 (by decide)
  have h9 : Entails.eval a c2164 := h 2163 (by decide)
  have h10 : Entails.eval a c4903 := h 4902 (by decide)
  have h11 : Entails.eval a c4951 := h 4950 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9515 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9515 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c2700, some c1413, some c690, some c2503, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9515 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9515 : lratChecker f9515 p9515 = .success := by decide +kernel
theorem unsat9515 : Unsatisfiable (PosFin 65) f9515 := by
  apply lratCheckerSound f9515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9515
  · intro a ha; simp [p9515] at ha; subst a; trivial
  · exact checked9515
theorem derived9515 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9515 := by
  apply localUnsat_implies_entails f9515 [c9347, c8435, c8445, c2700, c1413, c690, c2503] c9515 unsat9515 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c2700 := h 2699 (by decide)
  have h4 : Entails.eval a c1413 := h 1412 (by decide)
  have h5 : Entails.eval a c690 := h 689 (by decide)
  have h6 : Entails.eval a c2503 := h 2502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9516 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨63, by decide⟩, true), (⟨58, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9516 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9195, some c9438, some c8496, some c1403, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9516 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9516 : lratChecker f9516 p9516 = .success := by decide +kernel
theorem unsat9516 : Unsatisfiable (PosFin 65) f9516 := by
  apply lratCheckerSound f9516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9516
  · intro a ha; simp [p9516] at ha; subst a; trivial
  · exact checked9516
theorem derived9516 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9516 := by
  apply localUnsat_implies_entails f9516 [c9195, c9438, c8496, c1403] c9516 unsat9516 (by rfl) a
  have h0 : Entails.eval a c9195 := derived9195 a h
  have h1 : Entails.eval a c9438 := derived9438 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c1403 := h 1402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9517 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9517 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9482, some c9347, some c9441, some c9516, some c8435, some c8445, some c9515, some c1413, some c690, some c5078, some c4238, some c2563, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9517 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9517 : lratChecker f9517 p9517 = .success := by decide +kernel
theorem unsat9517 : Unsatisfiable (PosFin 65) f9517 := by
  apply lratCheckerSound f9517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9517
  · intro a ha; simp [p9517] at ha; subst a; trivial
  · exact checked9517
theorem derived9517 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9517 := by
  apply localUnsat_implies_entails f9517 [c9482, c9347, c9441, c9516, c8435, c8445, c9515, c1413, c690, c5078, c4238, c2563] c9517 unsat9517 (by rfl) a
  have h0 : Entails.eval a c9482 := derived9482 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9441 := derived9441 a h
  have h3 : Entails.eval a c9516 := derived9516 a h
  have h4 : Entails.eval a c8435 := derived8435 a h
  have h5 : Entails.eval a c8445 := derived8445 a h
  have h6 : Entails.eval a c9515 := derived9515 a h
  have h7 : Entails.eval a c1413 := h 1412 (by decide)
  have h8 : Entails.eval a c690 := h 689 (by decide)
  have h9 : Entails.eval a c5078 := h 5077 (by decide)
  have h10 : Entails.eval a c4238 := h 4237 (by decide)
  have h11 : Entails.eval a c2563 := h 2562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9518 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9518 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9510, some c9322, some c9482, some c9445, some c9514, some c9347, some c9433, some c9420, some c9517, some c2469, some c2492, some c1422, some c9516, some c8435, some c8445, some c9515, some c2459, some c1413, some c690, some c2564, some c4013, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9518 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9518 : lratChecker f9518 p9518 = .success := by decide +kernel
theorem unsat9518 : Unsatisfiable (PosFin 65) f9518 := by
  apply lratCheckerSound f9518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9518
  · intro a ha; simp [p9518] at ha; subst a; trivial
  · exact checked9518
theorem derived9518 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9518 := by
  apply localUnsat_implies_entails f9518 [c9494, c9510, c9322, c9482, c9445, c9514, c9347, c9433, c9420, c9517, c2469, c2492, c1422, c9516, c8435, c8445, c9515, c2459, c1413, c690, c2564, c4013] c9518 unsat9518 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9510 := derived9510 a h
  have h2 : Entails.eval a c9322 := derived9322 a h
  have h3 : Entails.eval a c9482 := derived9482 a h
  have h4 : Entails.eval a c9445 := derived9445 a h
  have h5 : Entails.eval a c9514 := derived9514 a h
  have h6 : Entails.eval a c9347 := derived9347 a h
  have h7 : Entails.eval a c9433 := derived9433 a h
  have h8 : Entails.eval a c9420 := derived9420 a h
  have h9 : Entails.eval a c9517 := derived9517 a h
  have h10 : Entails.eval a c2469 := h 2468 (by decide)
  have h11 : Entails.eval a c2492 := h 2491 (by decide)
  have h12 : Entails.eval a c1422 := h 1421 (by decide)
  have h13 : Entails.eval a c9516 := derived9516 a h
  have h14 : Entails.eval a c8435 := derived8435 a h
  have h15 : Entails.eval a c8445 := derived8445 a h
  have h16 : Entails.eval a c9515 := derived9515 a h
  have h17 : Entails.eval a c2459 := h 2458 (by decide)
  have h18 : Entails.eval a c1413 := h 1412 (by decide)
  have h19 : Entails.eval a c690 := h 689 (by decide)
  have h20 : Entails.eval a c2564 := h 2563 (by decide)
  have h21 : Entails.eval a c4013 := h 4012 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9519 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨50, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9519 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2179, some c9441, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9519 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9519 : lratChecker f9519 p9519 = .success := by decide +kernel
theorem unsat9519 : Unsatisfiable (PosFin 65) f9519 := by
  apply lratCheckerSound f9519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9519
  · intro a ha; simp [p9519] at ha; subst a; trivial
  · exact checked9519
theorem derived9519 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9519 := by
  apply localUnsat_implies_entails f9519 [c2179, c9441] c9519 unsat9519 (by rfl) a
  have h0 : Entails.eval a c2179 := h 2178 (by decide)
  have h1 : Entails.eval a c9441 := derived9441 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9520 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨62, by decide⟩, true), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9520 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9519, some c2483, some c2477, some c1422, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9520 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9520 : lratChecker f9520 p9520 = .success := by decide +kernel
theorem unsat9520 : Unsatisfiable (PosFin 65) f9520 := by
  apply lratCheckerSound f9520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9520
  · intro a ha; simp [p9520] at ha; subst a; trivial
  · exact checked9520
theorem derived9520 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9520 := by
  apply localUnsat_implies_entails f9520 [c9347, c9519, c2483, c2477, c1422] c9520 unsat9520 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9519 := derived9519 a h
  have h2 : Entails.eval a c2483 := h 2482 (by decide)
  have h3 : Entails.eval a c2477 := h 2476 (by decide)
  have h4 : Entails.eval a c1422 := h 1421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9521 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨58, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9521 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9482, some c3577, some c9441, some c3578, some c3598, some c1448, some c9516, some c9427, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9521 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9521 : lratChecker f9521 p9521 = .success := by decide +kernel
theorem unsat9521 : Unsatisfiable (PosFin 65) f9521 := by
  apply lratCheckerSound f9521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9521
  · intro a ha; simp [p9521] at ha; subst a; trivial
  · exact checked9521
theorem derived9521 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9521 := by
  apply localUnsat_implies_entails f9521 [c9482, c3577, c9441, c3578, c3598, c1448, c9516, c9427] c9521 unsat9521 (by rfl) a
  have h0 : Entails.eval a c9482 := derived9482 a h
  have h1 : Entails.eval a c3577 := h 3576 (by decide)
  have h2 : Entails.eval a c9441 := derived9441 a h
  have h3 : Entails.eval a c3578 := h 3577 (by decide)
  have h4 : Entails.eval a c3598 := h 3597 (by decide)
  have h5 : Entails.eval a c1448 := h 1447 (by decide)
  have h6 : Entails.eval a c9516 := derived9516 a h
  have h7 : Entails.eval a c9427 := derived9427 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9522 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9522 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9514, some c9494, some c9510, some c9322, some c9347, some c9445, some c9482, some c9520, some c9433, some c9420, some c9518, some c9521, some c2469, some c2492, some c2485, some c2484, some c1422, some c1449, some c2499, some c9516, some c9427, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9522 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9522 : lratChecker f9522 p9522 = .success := by decide +kernel
theorem unsat9522 : Unsatisfiable (PosFin 65) f9522 := by
  apply lratCheckerSound f9522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9522
  · intro a ha; simp [p9522] at ha; subst a; trivial
  · exact checked9522
theorem derived9522 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9522 := by
  apply localUnsat_implies_entails f9522 [c9514, c9494, c9510, c9322, c9347, c9445, c9482, c9520, c9433, c9420, c9518, c9521, c2469, c2492, c2485, c2484, c1422, c1449, c2499, c9516, c9427] c9522 unsat9522 (by rfl) a
  have h0 : Entails.eval a c9514 := derived9514 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9510 := derived9510 a h
  have h3 : Entails.eval a c9322 := derived9322 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9445 := derived9445 a h
  have h6 : Entails.eval a c9482 := derived9482 a h
  have h7 : Entails.eval a c9520 := derived9520 a h
  have h8 : Entails.eval a c9433 := derived9433 a h
  have h9 : Entails.eval a c9420 := derived9420 a h
  have h10 : Entails.eval a c9518 := derived9518 a h
  have h11 : Entails.eval a c9521 := derived9521 a h
  have h12 : Entails.eval a c2469 := h 2468 (by decide)
  have h13 : Entails.eval a c2492 := h 2491 (by decide)
  have h14 : Entails.eval a c2485 := h 2484 (by decide)
  have h15 : Entails.eval a c2484 := h 2483 (by decide)
  have h16 : Entails.eval a c1422 := h 1421 (by decide)
  have h17 : Entails.eval a c1449 := h 1448 (by decide)
  have h18 : Entails.eval a c2499 := h 2498 (by decide)
  have h19 : Entails.eval a c9516 := derived9516 a h
  have h20 : Entails.eval a c9427 := derived9427 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9523 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9523 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c692, some c690, some c2668, some c2159, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9523 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9523 : lratChecker f9523 p9523 = .success := by decide +kernel
theorem unsat9523 : Unsatisfiable (PosFin 65) f9523 := by
  apply lratCheckerSound f9523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9523
  · intro a ha; simp [p9523] at ha; subst a; trivial
  · exact checked9523
theorem derived9523 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9523 := by
  apply localUnsat_implies_entails f9523 [c9347, c8435, c8445, c692, c690, c2668, c2159] c9523 unsat9523 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c690 := h 689 (by decide)
  have h5 : Entails.eval a c2668 := h 2667 (by decide)
  have h6 : Entails.eval a c2159 := h 2158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9524 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9524 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9500, some c2682, some c2672, some c2693, some c2688, some c2686, some c9441, some c9523, some c9195, some c9438, some c8496, some c2660, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9524 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9524 : lratChecker f9524 p9524 = .success := by decide +kernel
theorem unsat9524 : Unsatisfiable (PosFin 65) f9524 := by
  apply lratCheckerSound f9524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9524
  · intro a ha; simp [p9524] at ha; subst a; trivial
  · exact checked9524
theorem derived9524 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9524 := by
  apply localUnsat_implies_entails f9524 [c9347, c9500, c2682, c2672, c2693, c2688, c2686, c9441, c9523, c9195, c9438, c8496, c2660] c9524 unsat9524 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9500 := derived9500 a h
  have h2 : Entails.eval a c2682 := h 2681 (by decide)
  have h3 : Entails.eval a c2672 := h 2671 (by decide)
  have h4 : Entails.eval a c2693 := h 2692 (by decide)
  have h5 : Entails.eval a c2688 := h 2687 (by decide)
  have h6 : Entails.eval a c2686 := h 2685 (by decide)
  have h7 : Entails.eval a c9441 := derived9441 a h
  have h8 : Entails.eval a c9523 := derived9523 a h
  have h9 : Entails.eval a c9195 := derived9195 a h
  have h10 : Entails.eval a c9438 := derived9438 a h
  have h11 : Entails.eval a c8496 := derived8496 a h
  have h12 : Entails.eval a c2660 := h 2659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9525 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9525 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c2459, some c692, some c690, some c2564, some c2503, some c4013, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9525 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9525 : lratChecker f9525 p9525 = .success := by decide +kernel
theorem unsat9525 : Unsatisfiable (PosFin 65) f9525 := by
  apply lratCheckerSound f9525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9525
  · intro a ha; simp [p9525] at ha; subst a; trivial
  · exact checked9525
theorem derived9525 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9525 := by
  apply localUnsat_implies_entails f9525 [c9347, c8435, c8445, c2459, c692, c690, c2564, c2503, c4013] c9525 unsat9525 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c2459 := h 2458 (by decide)
  have h4 : Entails.eval a c692 := h 691 (by decide)
  have h5 : Entails.eval a c690 := h 689 (by decide)
  have h6 : Entails.eval a c2564 := h 2563 (by decide)
  have h7 : Entails.eval a c2503 := h 2502 (by decide)
  have h8 : Entails.eval a c4013 := h 4012 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9526 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9526 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9522, some c9514, some c9494, some c9510, some c9322, some c9347, some c9500, some c2682, some c2672, some c2693, some c2688, some c2686, some c9433, some c9524, some c2496, some c2847, some c9525, some c9195, some c9438, some c8496, some c2660, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9526 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9526 : lratChecker f9526 p9526 = .success := by decide +kernel
theorem unsat9526 : Unsatisfiable (PosFin 65) f9526 := by
  apply lratCheckerSound f9526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9526
  · intro a ha; simp [p9526] at ha; subst a; trivial
  · exact checked9526
theorem derived9526 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9526 := by
  apply localUnsat_implies_entails f9526 [c9522, c9514, c9494, c9510, c9322, c9347, c9500, c2682, c2672, c2693, c2688, c2686, c9433, c9524, c2496, c2847, c9525, c9195, c9438, c8496, c2660] c9526 unsat9526 (by rfl) a
  have h0 : Entails.eval a c9522 := derived9522 a h
  have h1 : Entails.eval a c9514 := derived9514 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9510 := derived9510 a h
  have h4 : Entails.eval a c9322 := derived9322 a h
  have h5 : Entails.eval a c9347 := derived9347 a h
  have h6 : Entails.eval a c9500 := derived9500 a h
  have h7 : Entails.eval a c2682 := h 2681 (by decide)
  have h8 : Entails.eval a c2672 := h 2671 (by decide)
  have h9 : Entails.eval a c2693 := h 2692 (by decide)
  have h10 : Entails.eval a c2688 := h 2687 (by decide)
  have h11 : Entails.eval a c2686 := h 2685 (by decide)
  have h12 : Entails.eval a c9433 := derived9433 a h
  have h13 : Entails.eval a c9524 := derived9524 a h
  have h14 : Entails.eval a c2496 := h 2495 (by decide)
  have h15 : Entails.eval a c2847 := h 2846 (by decide)
  have h16 : Entails.eval a c9525 := derived9525 a h
  have h17 : Entails.eval a c9195 := derived9195 a h
  have h18 : Entails.eval a c9438 := derived9438 a h
  have h19 : Entails.eval a c8496 := derived8496 a h
  have h20 : Entails.eval a c2660 := h 2659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9527 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9527 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4967, some c2876, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9527 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9527 : lratChecker f9527 p9527 = .success := by decide +kernel
theorem unsat9527 : Unsatisfiable (PosFin 65) f9527 := by
  apply lratCheckerSound f9527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9527
  · intro a ha; simp [p9527] at ha; subst a; trivial
  · exact checked9527
theorem derived9527 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9527 := by
  apply localUnsat_implies_entails f9527 [c4967, c2876] c9527 unsat9527 (by rfl) a
  have h0 : Entails.eval a c4967 := h 4966 (by decide)
  have h1 : Entails.eval a c2876 := h 2875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9528 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9528 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c692, some c690, some c2161, some c2160, some c2159, some c2875, some c5093, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9528 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9528 : lratChecker f9528 p9528 = .success := by decide +kernel
theorem unsat9528 : Unsatisfiable (PosFin 65) f9528 := by
  apply lratCheckerSound f9528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9528
  · intro a ha; simp [p9528] at ha; subst a; trivial
  · exact checked9528
theorem derived9528 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9528 := by
  apply localUnsat_implies_entails f9528 [c9347, c8435, c8445, c692, c690, c2161, c2160, c2159, c2875, c5093] c9528 unsat9528 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c692 := h 691 (by decide)
  have h4 : Entails.eval a c690 := h 689 (by decide)
  have h5 : Entails.eval a c2161 := h 2160 (by decide)
  have h6 : Entails.eval a c2160 := h 2159 (by decide)
  have h7 : Entails.eval a c2159 := h 2158 (by decide)
  have h8 : Entails.eval a c2875 := h 2874 (by decide)
  have h9 : Entails.eval a c5093 := h 5092 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9529 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9529 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9527, some c3577, some c9441, some c3598, some c9528, some c9195, some c9438, some c8496, some c2154, some c8510, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9529 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9529 : lratChecker f9529 p9529 = .success := by decide +kernel
theorem unsat9529 : Unsatisfiable (PosFin 65) f9529 := by
  apply lratCheckerSound f9529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9529
  · intro a ha; simp [p9529] at ha; subst a; trivial
  · exact checked9529
theorem derived9529 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9529 := by
  apply localUnsat_implies_entails f9529 [c9347, c9527, c3577, c9441, c3598, c9528, c9195, c9438, c8496, c2154, c8510] c9529 unsat9529 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9527 := derived9527 a h
  have h2 : Entails.eval a c3577 := h 3576 (by decide)
  have h3 : Entails.eval a c9441 := derived9441 a h
  have h4 : Entails.eval a c3598 := h 3597 (by decide)
  have h5 : Entails.eval a c9528 := derived9528 a h
  have h6 : Entails.eval a c9195 := derived9195 a h
  have h7 : Entails.eval a c9438 := derived9438 a h
  have h8 : Entails.eval a c8496 := derived8496 a h
  have h9 : Entails.eval a c2154 := h 2153 (by decide)
  have h10 : Entails.eval a c8510 := derived8510 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9530 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9530 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c8435, some c8445, some c2459, some c690, some c2462, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9530 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9530 : lratChecker f9530 p9530 = .success := by decide +kernel
theorem unsat9530 : Unsatisfiable (PosFin 65) f9530 := by
  apply lratCheckerSound f9530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9530
  · intro a ha; simp [p9530] at ha; subst a; trivial
  · exact checked9530
theorem derived9530 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9530 := by
  apply localUnsat_implies_entails f9530 [c9347, c8435, c8445, c2459, c690, c2462] c9530 unsat9530 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8445 := derived8445 a h
  have h3 : Entails.eval a c2459 := h 2458 (by decide)
  have h4 : Entails.eval a c690 := h 689 (by decide)
  have h5 : Entails.eval a c2462 := h 2461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9531 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9531 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9526, some c9522, some c9514, some c9494, some c9510, some c9322, some c9347, some c9433, some c9527, some c9529, some c9478, some c2469, some c2492, some c2860, some c2485, some c2497, some c2851, some c2847, some c9530, some c9195, some c9438, some c8496, some c2825, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9531 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9531 : lratChecker f9531 p9531 = .success := by decide +kernel
theorem unsat9531 : Unsatisfiable (PosFin 65) f9531 := by
  apply lratCheckerSound f9531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9531
  · intro a ha; simp [p9531] at ha; subst a; trivial
  · exact checked9531
theorem derived9531 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9531 := by
  apply localUnsat_implies_entails f9531 [c9526, c9522, c9514, c9494, c9510, c9322, c9347, c9433, c9527, c9529, c9478, c2469, c2492, c2860, c2485, c2497, c2851, c2847, c9530, c9195, c9438, c8496, c2825] c9531 unsat9531 (by rfl) a
  have h0 : Entails.eval a c9526 := derived9526 a h
  have h1 : Entails.eval a c9522 := derived9522 a h
  have h2 : Entails.eval a c9514 := derived9514 a h
  have h3 : Entails.eval a c9494 := derived9494 a h
  have h4 : Entails.eval a c9510 := derived9510 a h
  have h5 : Entails.eval a c9322 := derived9322 a h
  have h6 : Entails.eval a c9347 := derived9347 a h
  have h7 : Entails.eval a c9433 := derived9433 a h
  have h8 : Entails.eval a c9527 := derived9527 a h
  have h9 : Entails.eval a c9529 := derived9529 a h
  have h10 : Entails.eval a c9478 := derived9478 a h
  have h11 : Entails.eval a c2469 := h 2468 (by decide)
  have h12 : Entails.eval a c2492 := h 2491 (by decide)
  have h13 : Entails.eval a c2860 := h 2859 (by decide)
  have h14 : Entails.eval a c2485 := h 2484 (by decide)
  have h15 : Entails.eval a c2497 := h 2496 (by decide)
  have h16 : Entails.eval a c2851 := h 2850 (by decide)
  have h17 : Entails.eval a c2847 := h 2846 (by decide)
  have h18 : Entails.eval a c9530 := derived9530 a h
  have h19 : Entails.eval a c9195 := derived9195 a h
  have h20 : Entails.eval a c9438 := derived9438 a h
  have h21 : Entails.eval a c8496 := derived8496 a h
  have h22 : Entails.eval a c2825 := h 2824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9532 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9532 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9347, some c9510, some c9322, some c9514, some c9522, some c9526, some c9531, some c9463, some c9519, some c2859, some c2477, some c4905, some c4952, some c3339, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9532 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9532 : lratChecker f9532 p9532 = .success := by decide +kernel
theorem unsat9532 : Unsatisfiable (PosFin 65) f9532 := by
  apply lratCheckerSound f9532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9532
  · intro a ha; simp [p9532] at ha; subst a; trivial
  · exact checked9532
theorem derived9532 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9532 := by
  apply localUnsat_implies_entails f9532 [c9494, c9347, c9510, c9322, c9514, c9522, c9526, c9531, c9463, c9519, c2859, c2477, c4905, c4952, c3339] c9532 unsat9532 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9510 := derived9510 a h
  have h3 : Entails.eval a c9322 := derived9322 a h
  have h4 : Entails.eval a c9514 := derived9514 a h
  have h5 : Entails.eval a c9522 := derived9522 a h
  have h6 : Entails.eval a c9526 := derived9526 a h
  have h7 : Entails.eval a c9531 := derived9531 a h
  have h8 : Entails.eval a c9463 := derived9463 a h
  have h9 : Entails.eval a c9519 := derived9519 a h
  have h10 : Entails.eval a c2859 := h 2858 (by decide)
  have h11 : Entails.eval a c2477 := h 2476 (by decide)
  have h12 : Entails.eval a c4905 := h 4904 (by decide)
  have h13 : Entails.eval a c4952 := h 4951 (by decide)
  have h14 : Entails.eval a c3339 := h 3338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9533 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨64, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9533 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c1275, some c1274, some c1303, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9533 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9533 : lratChecker f9533 p9533 = .success := by decide +kernel
theorem unsat9533 : Unsatisfiable (PosFin 65) f9533 := by
  apply lratCheckerSound f9533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9533
  · intro a ha; simp [p9533] at ha; subst a; trivial
  · exact checked9533
theorem derived9533 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9533 := by
  apply localUnsat_implies_entails f9533 [c8269, c7994, c1275, c1274, c1303] c9533 unsat9533 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c1275 := h 1274 (by decide)
  have h3 : Entails.eval a c1274 := h 1273 (by decide)
  have h4 : Entails.eval a c1303 := h 1302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9534 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9534 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9347, some c9532, some c7994, some c8269, some c9467, some c9533, some c8383, some c9416, some c2176, some c1367, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9534 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9534 : lratChecker f9534 p9534 = .success := by decide +kernel
theorem unsat9534 : Unsatisfiable (PosFin 65) f9534 := by
  apply lratCheckerSound f9534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9534
  · intro a ha; simp [p9534] at ha; subst a; trivial
  · exact checked9534
theorem derived9534 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9534 := by
  apply localUnsat_implies_entails f9534 [c9494, c9347, c9532, c7994, c8269, c9467, c9533, c8383, c9416, c2176, c1367] c9534 unsat9534 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9532 := derived9532 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c9467 := derived9467 a h
  have h6 : Entails.eval a c9533 := derived9533 a h
  have h7 : Entails.eval a c8383 := derived8383 a h
  have h8 : Entails.eval a c9416 := derived9416 a h
  have h9 : Entails.eval a c2176 := h 2175 (by decide)
  have h10 : Entails.eval a c1367 := h 1366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9535 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, false), (⟨58, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9535 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3764, some c3769, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9535 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9535 : lratChecker f9535 p9535 = .success := by decide +kernel
theorem unsat9535 : Unsatisfiable (PosFin 65) f9535 := by
  apply lratCheckerSound f9535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9535
  · intro a ha; simp [p9535] at ha; subst a; trivial
  · exact checked9535
theorem derived9535 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9535 := by
  apply localUnsat_implies_entails f9535 [c3764, c3769] c9535 unsat9535 (by rfl) a
  have h0 : Entails.eval a c3764 := h 3763 (by decide)
  have h1 : Entails.eval a c3769 := h 3768 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9536 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨52, by decide⟩, true), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9536 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2163, some c2174, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9536 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9536 : lratChecker f9536 p9536 = .success := by decide +kernel
theorem unsat9536 : Unsatisfiable (PosFin 65) f9536 := by
  apply lratCheckerSound f9536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9536
  · intro a ha; simp [p9536] at ha; subst a; trivial
  · exact checked9536
theorem derived9536 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9536 := by
  apply localUnsat_implies_entails f9536 [c2163, c2174] c9536 unsat9536 (by rfl) a
  have h0 : Entails.eval a c2163 := h 2162 (by decide)
  have h1 : Entails.eval a c2174 := h 2173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9537 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9537 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4545, some c4550, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9537 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9537 : lratChecker f9537 p9537 = .success := by decide +kernel
theorem unsat9537 : Unsatisfiable (PosFin 65) f9537 := by
  apply lratCheckerSound f9537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9537
  · intro a ha; simp [p9537] at ha; subst a; trivial
  · exact checked9537
theorem derived9537 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9537 := by
  apply localUnsat_implies_entails f9537 [c4545, c4550] c9537 unsat9537 (by rfl) a
  have h0 : Entails.eval a c4545 := h 4544 (by decide)
  have h1 : Entails.eval a c4550 := h 4549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9538 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9538 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4968, some c2550, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9538 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9538 : lratChecker f9538 p9538 = .success := by decide +kernel
theorem unsat9538 : Unsatisfiable (PosFin 65) f9538 := by
  apply lratCheckerSound f9538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9538
  · intro a ha; simp [p9538] at ha; subst a; trivial
  · exact checked9538
theorem derived9538 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9538 := by
  apply localUnsat_implies_entails f9538 [c4968, c2550] c9538 unsat9538 (by rfl) a
  have h0 : Entails.eval a c4968 := h 4967 (by decide)
  have h1 : Entails.eval a c2550 := h 2549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9539 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, false), (⟨58, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9539 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9537, some c9538, some c2711, some c4956, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9539 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9539 : lratChecker f9539 p9539 = .success := by decide +kernel
theorem unsat9539 : Unsatisfiable (PosFin 65) f9539 := by
  apply lratCheckerSound f9539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9539
  · intro a ha; simp [p9539] at ha; subst a; trivial
  · exact checked9539
theorem derived9539 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9539 := by
  apply localUnsat_implies_entails f9539 [c9537, c9538, c2711, c4956] c9539 unsat9539 (by rfl) a
  have h0 : Entails.eval a c9537 := derived9537 a h
  have h1 : Entails.eval a c9538 := derived9538 a h
  have h2 : Entails.eval a c2711 := h 2710 (by decide)
  have h3 : Entails.eval a c4956 := h 4955 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9540 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9540 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1260, some c8824, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9540 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9540 : lratChecker f9540 p9540 = .success := by decide +kernel
theorem unsat9540 : Unsatisfiable (PosFin 65) f9540 := by
  apply lratCheckerSound f9540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9540
  · intro a ha; simp [p9540] at ha; subst a; trivial
  · exact checked9540
theorem derived9540 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9540 := by
  apply localUnsat_implies_entails f9540 [c1260, c8824] c9540 unsat9540 (by rfl) a
  have h0 : Entails.eval a c1260 := h 1259 (by decide)
  have h1 : Entails.eval a c8824 := derived8824 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9541 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9541 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9540, some c8813, some c8825, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9541 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9541 : lratChecker f9541 p9541 = .success := by decide +kernel
theorem unsat9541 : Unsatisfiable (PosFin 65) f9541 := by
  apply lratCheckerSound f9541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9541
  · intro a ha; simp [p9541] at ha; subst a; trivial
  · exact checked9541
theorem derived9541 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9541 := by
  apply localUnsat_implies_entails f9541 [c9540, c8813, c8825] c9541 unsat9541 (by rfl) a
  have h0 : Entails.eval a c9540 := derived9540 a h
  have h1 : Entails.eval a c8813 := derived8813 a h
  have h2 : Entails.eval a c8825 := derived8825 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9542 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9542 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5474, some c8820, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p9542 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9542 : lratChecker f9542 p9542 = .success := by decide +kernel
theorem unsat9542 : Unsatisfiable (PosFin 65) f9542 := by
  apply lratCheckerSound f9542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9542
  · intro a ha; simp [p9542] at ha; subst a; trivial
  · exact checked9542
theorem derived9542 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9542 := by
  apply localUnsat_implies_entails f9542 [c5474, c8820] c9542 unsat9542 (by rfl) a
  have h0 : Entails.eval a c5474 := h 5473 (by decide)
  have h1 : Entails.eval a c8820 := derived8820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9543 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨11, by decide⟩, false), (⟨61, by decide⟩, true), (⟨54, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9543 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9541, some c9542, some c200, some c2, some c194, some c6166, some c8897, some c73, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9543 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9543 : lratChecker f9543 p9543 = .success := by decide +kernel
theorem unsat9543 : Unsatisfiable (PosFin 65) f9543 := by
  apply lratCheckerSound f9543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9543
  · intro a ha; simp [p9543] at ha; subst a; trivial
  · exact checked9543
theorem derived9543 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9543 := by
  apply localUnsat_implies_entails f9543 [c9541, c9542, c200, c2, c194, c6166, c8897, c73] c9543 unsat9543 (by rfl) a
  have h0 : Entails.eval a c9541 := derived9541 a h
  have h1 : Entails.eval a c9542 := derived9542 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c6166 := h 6165 (by decide)
  have h6 : Entails.eval a c8897 := derived8897 a h
  have h7 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9544 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9544 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c195, some c1251, some c1254, some c876, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9544 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9544 : lratChecker f9544 p9544 = .success := by decide +kernel
theorem unsat9544 : Unsatisfiable (PosFin 65) f9544 := by
  apply lratCheckerSound f9544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9544
  · intro a ha; simp [p9544] at ha; subst a; trivial
  · exact checked9544
theorem derived9544 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9544 := by
  apply localUnsat_implies_entails f9544 [c195, c1251, c1254, c876] c9544 unsat9544 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c1251 := h 1250 (by decide)
  have h2 : Entails.eval a c1254 := h 1253 (by decide)
  have h3 : Entails.eval a c876 := h 875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9545 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9545 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9495, some c9497, some c1290, some c1288, some c1303, some c1299, some c1301, some c1276, some c1306, some c1295, some c9534, some c9347, some c1235, some c9535, some c3432, some c9539, some c9543, some c9115, some c2530, some c9544, some c8812, some c8715, some c3032, some c203, some c3026, some c5298, some c865, some c6148, some c59, some c3426, some c6363, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9545 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked9545 : lratChecker f9545 p9545 = .success := by decide +kernel
theorem unsat9545 : Unsatisfiable (PosFin 65) f9545 := by
  apply lratCheckerSound f9545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9545
  · intro a ha; simp [p9545] at ha; subst a; trivial
  · exact checked9545
theorem derived9545 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9545 := by
  apply localUnsat_implies_entails f9545 [c9494, c9495, c9497, c1290, c1288, c1303, c1299, c1301, c1276, c1306, c1295, c9534, c9347, c1235, c9535, c3432, c9539, c9543, c9115, c2530, c9544, c8812, c8715, c3032, c203, c3026, c5298, c865, c6148, c59, c3426, c6363] c9545 unsat9545 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9495 := derived9495 a h
  have h2 : Entails.eval a c9497 := derived9497 a h
  have h3 : Entails.eval a c1290 := h 1289 (by decide)
  have h4 : Entails.eval a c1288 := h 1287 (by decide)
  have h5 : Entails.eval a c1303 := h 1302 (by decide)
  have h6 : Entails.eval a c1299 := h 1298 (by decide)
  have h7 : Entails.eval a c1301 := h 1300 (by decide)
  have h8 : Entails.eval a c1276 := h 1275 (by decide)
  have h9 : Entails.eval a c1306 := h 1305 (by decide)
  have h10 : Entails.eval a c1295 := h 1294 (by decide)
  have h11 : Entails.eval a c9534 := derived9534 a h
  have h12 : Entails.eval a c9347 := derived9347 a h
  have h13 : Entails.eval a c1235 := h 1234 (by decide)
  have h14 : Entails.eval a c9535 := derived9535 a h
  have h15 : Entails.eval a c3432 := h 3431 (by decide)
  have h16 : Entails.eval a c9539 := derived9539 a h
  have h17 : Entails.eval a c9543 := derived9543 a h
  have h18 : Entails.eval a c9115 := derived9115 a h
  have h19 : Entails.eval a c2530 := h 2529 (by decide)
  have h20 : Entails.eval a c9544 := derived9544 a h
  have h21 : Entails.eval a c8812 := derived8812 a h
  have h22 : Entails.eval a c8715 := derived8715 a h
  have h23 : Entails.eval a c3032 := h 3031 (by decide)
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c3026 := h 3025 (by decide)
  have h26 : Entails.eval a c5298 := h 5297 (by decide)
  have h27 : Entails.eval a c865 := h 864 (by decide)
  have h28 : Entails.eval a c6148 := h 6147 (by decide)
  have h29 : Entails.eval a c59 := h 58 (by decide)
  have h30 : Entails.eval a c3426 := h 3425 (by decide)
  have h31 : Entails.eval a c6363 := h 6362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9546 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9546 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9347, some c9495, some c9497, some c1288, some c1290, some c1299, some c1303, some c1301, some c1276, some c9545, some c9477, some c2174, some c2173, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9546 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9546 : lratChecker f9546 p9546 = .success := by decide +kernel
theorem unsat9546 : Unsatisfiable (PosFin 65) f9546 := by
  apply lratCheckerSound f9546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9546
  · intro a ha; simp [p9546] at ha; subst a; trivial
  · exact checked9546
theorem derived9546 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9546 := by
  apply localUnsat_implies_entails f9546 [c9494, c9347, c9495, c9497, c1288, c1290, c1299, c1303, c1301, c1276, c9545, c9477, c2174, c2173] c9546 unsat9546 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9495 := derived9495 a h
  have h3 : Entails.eval a c9497 := derived9497 a h
  have h4 : Entails.eval a c1288 := h 1287 (by decide)
  have h5 : Entails.eval a c1290 := h 1289 (by decide)
  have h6 : Entails.eval a c1299 := h 1298 (by decide)
  have h7 : Entails.eval a c1303 := h 1302 (by decide)
  have h8 : Entails.eval a c1301 := h 1300 (by decide)
  have h9 : Entails.eval a c1276 := h 1275 (by decide)
  have h10 : Entails.eval a c9545 := derived9545 a h
  have h11 : Entails.eval a c9477 := derived9477 a h
  have h12 : Entails.eval a c2174 := h 2173 (by decide)
  have h13 : Entails.eval a c2173 := h 2172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9547 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9547 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c196, some c365, some c340, some c5356, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9547 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9547 : lratChecker f9547 p9547 = .success := by decide +kernel
theorem unsat9547 : Unsatisfiable (PosFin 65) f9547 := by
  apply lratCheckerSound f9547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9547
  · intro a ha; simp [p9547] at ha; subst a; trivial
  · exact checked9547
theorem derived9547 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9547 := by
  apply localUnsat_implies_entails f9547 [c196, c365, c340, c5356] c9547 unsat9547 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c5356 := h 5355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9548 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9548 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c366, some c204, some c368, some c3033, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9548 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9548 : lratChecker f9548 p9548 = .success := by decide +kernel
theorem unsat9548 : Unsatisfiable (PosFin 65) f9548 := by
  apply lratCheckerSound f9548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9548
  · intro a ha; simp [p9548] at ha; subst a; trivial
  · exact checked9548
theorem derived9548 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9548 := by
  apply localUnsat_implies_entails f9548 [c366, c204, c368, c3033] c9548 unsat9548 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c3033 := h 3032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9549 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9549 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c1300, some c9347, some c2531, some c2550, some c3769, some c5105, some c2710, some c9547, some c9548, some c3077, some c3183, some c1252, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9549 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9549 : lratChecker f9549 p9549 = .success := by decide +kernel
theorem unsat9549 : Unsatisfiable (PosFin 65) f9549 := by
  apply lratCheckerSound f9549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9549
  · intro a ha; simp [p9549] at ha; subst a; trivial
  · exact checked9549
theorem derived9549 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9549 := by
  apply localUnsat_implies_entails f9549 [c9494, c1300, c9347, c2531, c2550, c3769, c5105, c2710, c9547, c9548, c3077, c3183, c1252] c9549 unsat9549 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c1300 := h 1299 (by decide)
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2531 := h 2530 (by decide)
  have h4 : Entails.eval a c2550 := h 2549 (by decide)
  have h5 : Entails.eval a c3769 := h 3768 (by decide)
  have h6 : Entails.eval a c5105 := h 5104 (by decide)
  have h7 : Entails.eval a c2710 := h 2709 (by decide)
  have h8 : Entails.eval a c9547 := derived9547 a h
  have h9 : Entails.eval a c9548 := derived9548 a h
  have h10 : Entails.eval a c3077 := h 3076 (by decide)
  have h11 : Entails.eval a c3183 := h 3182 (by decide)
  have h12 : Entails.eval a c1252 := h 1251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9550 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9550 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c633, some c619, some c1249, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9550 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9550 : lratChecker f9550 p9550 = .success := by decide +kernel
theorem unsat9550 : Unsatisfiable (PosFin 65) f9550 := by
  apply lratCheckerSound f9550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9550
  · intro a ha; simp [p9550] at ha; subst a; trivial
  · exact checked9550
theorem derived9550 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9550 := by
  apply localUnsat_implies_entails f9550 [c633, c619, c1249] c9550 unsat9550 (by rfl) a
  have h0 : Entails.eval a c633 := h 632 (by decide)
  have h1 : Entails.eval a c619 := h 618 (by decide)
  have h2 : Entails.eval a c1249 := h 1248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived9550

end CochromaticTwenty.Certificates.FixedCore0
