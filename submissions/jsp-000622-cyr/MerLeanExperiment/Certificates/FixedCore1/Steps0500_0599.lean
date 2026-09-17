import MerLeanExperiment.Certificates.FixedCore1.Steps0400_0499

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6381 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3321, some c3336, some c3348, some c3391, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6381 : lratChecker f6381 p6381 = .success := by decide +kernel
theorem unsat6381 : Unsatisfiable (PosFin 65) f6381 := by
  apply lratCheckerSound f6381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6381
  · intro a ha; simp [p6381] at ha; subst a; trivial
  · exact checked6381
theorem derived6381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6381 := by
  apply localUnsat_implies_entails f6381 [c3321, c3336, c3348, c3391] c6381 unsat6381 (by rfl) a
  have h0 : Entails.eval a c3321 := h 3320 (by decide)
  have h1 : Entails.eval a c3336 := h 3335 (by decide)
  have h2 : Entails.eval a c3348 := h 3347 (by decide)
  have h3 : Entails.eval a c3391 := h 3390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6382 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨47, by decide⟩, true), (⟨51, by decide⟩, false), (⟨37, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3062, some c2802, some c3069, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p6382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6382 : lratChecker f6382 p6382 = .success := by decide +kernel
theorem unsat6382 : Unsatisfiable (PosFin 65) f6382 := by
  apply lratCheckerSound f6382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6382
  · intro a ha; simp [p6382] at ha; subst a; trivial
  · exact checked6382
theorem derived6382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6382 := by
  apply localUnsat_implies_entails f6382 [c3062, c2802, c3069] c6382 unsat6382 (by rfl) a
  have h0 : Entails.eval a c3062 := h 3061 (by decide)
  have h1 : Entails.eval a c2802 := h 2801 (by decide)
  have h2 : Entails.eval a c3069 := h 3068 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6383 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨47, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨37, by decide⟩, true), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6381, some c6382, some c2907, some c3125, some c2929, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6383 : lratChecker f6383 p6383 = .success := by decide +kernel
theorem unsat6383 : Unsatisfiable (PosFin 65) f6383 := by
  apply lratCheckerSound f6383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6383
  · intro a ha; simp [p6383] at ha; subst a; trivial
  · exact checked6383
theorem derived6383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6383 := by
  apply localUnsat_implies_entails f6383 [c6381, c6382, c2907, c3125, c2929] c6383 unsat6383 (by rfl) a
  have h0 : Entails.eval a c6381 := derived6381 a h
  have h1 : Entails.eval a c6382 := derived6382 a h
  have h2 : Entails.eval a c2907 := h 2906 (by decide)
  have h3 : Entails.eval a c3125 := h 3124 (by decide)
  have h4 : Entails.eval a c2929 := h 2928 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6384 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨59, by decide⟩, false), (⟨42, by decide⟩, false), (⟨62, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2944, some c2929, some c2735, some c2796, some c3312, some c3193, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p6384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6384 : lratChecker f6384 p6384 = .success := by decide +kernel
theorem unsat6384 : Unsatisfiable (PosFin 65) f6384 := by
  apply lratCheckerSound f6384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6384
  · intro a ha; simp [p6384] at ha; subst a; trivial
  · exact checked6384
theorem derived6384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6384 := by
  apply localUnsat_implies_entails f6384 [c2944, c2929, c2735, c2796, c3312, c3193] c6384 unsat6384 (by rfl) a
  have h0 : Entails.eval a c2944 := h 2943 (by decide)
  have h1 : Entails.eval a c2929 := h 2928 (by decide)
  have h2 : Entails.eval a c2735 := h 2734 (by decide)
  have h3 : Entails.eval a c2796 := h 2795 (by decide)
  have h4 : Entails.eval a c3312 := h 3311 (by decide)
  have h5 : Entails.eval a c3193 := h 3192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6385 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨52, by decide⟩, false), (⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2833, some c2839, some c2842, some c3258, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p6385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6385 : lratChecker f6385 p6385 = .success := by decide +kernel
theorem unsat6385 : Unsatisfiable (PosFin 65) f6385 := by
  apply lratCheckerSound f6385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6385
  · intro a ha; simp [p6385] at ha; subst a; trivial
  · exact checked6385
theorem derived6385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6385 := by
  apply localUnsat_implies_entails f6385 [c2833, c2839, c2842, c3258] c6385 unsat6385 (by rfl) a
  have h0 : Entails.eval a c2833 := h 2832 (by decide)
  have h1 : Entails.eval a c2839 := h 2838 (by decide)
  have h2 : Entails.eval a c2842 := h 2841 (by decide)
  have h3 : Entails.eval a c3258 := h 3257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6386 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨22, by decide⟩, false), (⟨28, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3221, some c3193, some c3276, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p6386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6386 : lratChecker f6386 p6386 = .success := by decide +kernel
theorem unsat6386 : Unsatisfiable (PosFin 65) f6386 := by
  apply lratCheckerSound f6386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6386
  · intro a ha; simp [p6386] at ha; subst a; trivial
  · exact checked6386
theorem derived6386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6386 := by
  apply localUnsat_implies_entails f6386 [c3221, c3193, c3276] c6386 unsat6386 (by rfl) a
  have h0 : Entails.eval a c3221 := h 3220 (by decide)
  have h1 : Entails.eval a c3193 := h 3192 (by decide)
  have h2 : Entails.eval a c3276 := h 3275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6387 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, true), (⟨42, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2728, some c2735, some c3420, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p6387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6387 : lratChecker f6387 p6387 = .success := by decide +kernel
theorem unsat6387 : Unsatisfiable (PosFin 65) f6387 := by
  apply lratCheckerSound f6387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6387
  · intro a ha; simp [p6387] at ha; subst a; trivial
  · exact checked6387
theorem derived6387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6387 := by
  apply localUnsat_implies_entails f6387 [c2728, c2735, c3420] c6387 unsat6387 (by rfl) a
  have h0 : Entails.eval a c2728 := h 2727 (by decide)
  have h1 : Entails.eval a c2735 := h 2734 (by decide)
  have h2 : Entails.eval a c3420 := h 3419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6388 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4516, some c6380, some c4380, some c4394, some c6379, some c6377, some c6371, some c5834, some c4839, some c5597, some c4536, some c4892, some c3429, some c5313, some c4542, some c4635, some c3940, some c4419, some c5801, some c4410, some c6383, some c6385, some c6384, some c6387, some c3221, some c6386, some c3315, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked6388 : lratChecker f6388 p6388 = .success := by decide +kernel
theorem unsat6388 : Unsatisfiable (PosFin 65) f6388 := by
  apply lratCheckerSound f6388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6388
  · intro a ha; simp [p6388] at ha; subst a; trivial
  · exact checked6388
theorem derived6388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6388 := by
  apply localUnsat_implies_entails f6388 [c6227, c4516, c6380, c4380, c4394, c6379, c6377, c6371, c5834, c4839, c5597, c4536, c4892, c3429, c5313, c4542, c4635, c3940, c4419, c5801, c4410, c6383, c6385, c6384, c6387, c3221, c6386, c3315] c6388 unsat6388 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4516 := h 4515 (by decide)
  have h2 : Entails.eval a c6380 := derived6380 a h
  have h3 : Entails.eval a c4380 := h 4379 (by decide)
  have h4 : Entails.eval a c4394 := h 4393 (by decide)
  have h5 : Entails.eval a c6379 := derived6379 a h
  have h6 : Entails.eval a c6377 := derived6377 a h
  have h7 : Entails.eval a c6371 := derived6371 a h
  have h8 : Entails.eval a c5834 := h 5833 (by decide)
  have h9 : Entails.eval a c4839 := h 4838 (by decide)
  have h10 : Entails.eval a c5597 := h 5596 (by decide)
  have h11 : Entails.eval a c4536 := h 4535 (by decide)
  have h12 : Entails.eval a c4892 := h 4891 (by decide)
  have h13 : Entails.eval a c3429 := h 3428 (by decide)
  have h14 : Entails.eval a c5313 := h 5312 (by decide)
  have h15 : Entails.eval a c4542 := h 4541 (by decide)
  have h16 : Entails.eval a c4635 := h 4634 (by decide)
  have h17 : Entails.eval a c3940 := h 3939 (by decide)
  have h18 : Entails.eval a c4419 := h 4418 (by decide)
  have h19 : Entails.eval a c5801 := h 5800 (by decide)
  have h20 : Entails.eval a c4410 := h 4409 (by decide)
  have h21 : Entails.eval a c6383 := derived6383 a h
  have h22 : Entails.eval a c6385 := derived6385 a h
  have h23 : Entails.eval a c6384 := derived6384 a h
  have h24 : Entails.eval a c6387 := derived6387 a h
  have h25 : Entails.eval a c3221 := h 3220 (by decide)
  have h26 : Entails.eval a c6386 := derived6386 a h
  have h27 : Entails.eval a c3315 := h 3314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6389 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨50, by decide⟩, true), (⟨42, by decide⟩, false), (⟨51, by decide⟩, true), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2688, some c2795, some c2798, some c3025, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6389 : lratChecker f6389 p6389 = .success := by decide +kernel
theorem unsat6389 : Unsatisfiable (PosFin 65) f6389 := by
  apply lratCheckerSound f6389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6389
  · intro a ha; simp [p6389] at ha; subst a; trivial
  · exact checked6389
theorem derived6389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6389 := by
  apply localUnsat_implies_entails f6389 [c2688, c2795, c2798, c3025] c6389 unsat6389 (by rfl) a
  have h0 : Entails.eval a c2688 := h 2687 (by decide)
  have h1 : Entails.eval a c2795 := h 2794 (by decide)
  have h2 : Entails.eval a c2798 := h 2797 (by decide)
  have h3 : Entails.eval a c3025 := h 3024 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6390 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨47, by decide⟩, true), (⟨51, by decide⟩, true), (⟨37, by decide⟩, true), (⟨46, by decide⟩, false), (⟨35, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2974, some c3023, some c2784, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6390 : lratChecker f6390 p6390 = .success := by decide +kernel
theorem unsat6390 : Unsatisfiable (PosFin 65) f6390 := by
  apply lratCheckerSound f6390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6390
  · intro a ha; simp [p6390] at ha; subst a; trivial
  · exact checked6390
theorem derived6390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6390 := by
  apply localUnsat_implies_entails f6390 [c2974, c3023, c2784] c6390 unsat6390 (by rfl) a
  have h0 : Entails.eval a c2974 := h 2973 (by decide)
  have h1 : Entails.eval a c3023 := h 3022 (by decide)
  have h2 : Entails.eval a c2784 := h 2783 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6391 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, false), (⟨51, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2737, some c2803, some c3257, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6391 : lratChecker f6391 p6391 = .success := by decide +kernel
theorem unsat6391 : Unsatisfiable (PosFin 65) f6391 := by
  apply lratCheckerSound f6391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6391
  · intro a ha; simp [p6391] at ha; subst a; trivial
  · exact checked6391
theorem derived6391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6391 := by
  apply localUnsat_implies_entails f6391 [c2737, c2803, c3257] c6391 unsat6391 (by rfl) a
  have h0 : Entails.eval a c2737 := h 2736 (by decide)
  have h1 : Entails.eval a c2803 := h 2802 (by decide)
  have h2 : Entails.eval a c3257 := h 3256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6392 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c4516, some c6377, some c6379, some c6380, some c4380, some c6388, some c4837, some c3426, some c3931, some c4024, some c5379, some c5487, some c3935, some c4922, some c4447, some c4515, some c5604, some c6130, some c6389, some c6391, some c6390, some c2833, some c2842, some c3257, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked6392 : lratChecker f6392 p6392 = .success := by decide +kernel
theorem unsat6392 : Unsatisfiable (PosFin 65) f6392 := by
  apply lratCheckerSound f6392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6392
  · intro a ha; simp [p6392] at ha; subst a; trivial
  · exact checked6392
theorem derived6392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6392 := by
  apply localUnsat_implies_entails f6392 [c6371, c6227, c4516, c6377, c6379, c6380, c4380, c6388, c4837, c3426, c3931, c4024, c5379, c5487, c3935, c4922, c4447, c4515, c5604, c6130, c6389, c6391, c6390, c2833, c2842, c3257] c6392 unsat6392 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4516 := h 4515 (by decide)
  have h3 : Entails.eval a c6377 := derived6377 a h
  have h4 : Entails.eval a c6379 := derived6379 a h
  have h5 : Entails.eval a c6380 := derived6380 a h
  have h6 : Entails.eval a c4380 := h 4379 (by decide)
  have h7 : Entails.eval a c6388 := derived6388 a h
  have h8 : Entails.eval a c4837 := h 4836 (by decide)
  have h9 : Entails.eval a c3426 := h 3425 (by decide)
  have h10 : Entails.eval a c3931 := h 3930 (by decide)
  have h11 : Entails.eval a c4024 := h 4023 (by decide)
  have h12 : Entails.eval a c5379 := h 5378 (by decide)
  have h13 : Entails.eval a c5487 := h 5486 (by decide)
  have h14 : Entails.eval a c3935 := h 3934 (by decide)
  have h15 : Entails.eval a c4922 := h 4921 (by decide)
  have h16 : Entails.eval a c4447 := h 4446 (by decide)
  have h17 : Entails.eval a c4515 := h 4514 (by decide)
  have h18 : Entails.eval a c5604 := h 5603 (by decide)
  have h19 : Entails.eval a c6130 := derived6130 a h
  have h20 : Entails.eval a c6389 := derived6389 a h
  have h21 : Entails.eval a c6391 := derived6391 a h
  have h22 : Entails.eval a c6390 := derived6390 a h
  have h23 : Entails.eval a c2833 := h 2832 (by decide)
  have h24 : Entails.eval a c2842 := h 2841 (by decide)
  have h25 : Entails.eval a c3257 := h 3256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6393 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3831, some c3835, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6393 : lratChecker f6393 p6393 = .success := by decide +kernel
theorem unsat6393 : Unsatisfiable (PosFin 65) f6393 := by
  apply lratCheckerSound f6393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6393
  · intro a ha; simp [p6393] at ha; subst a; trivial
  · exact checked6393
theorem derived6393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6393 := by
  apply localUnsat_implies_entails f6393 [c6227, c3831, c3835] c6393 unsat6393 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3831 := h 3830 (by decide)
  have h2 : Entails.eval a c3835 := h 3834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6394 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨59, by decide⟩, false), (⟨40, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨46, by decide⟩, false), (⟨62, by decide⟩, false), (⟨49, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2834, some c2841, some c2844, some c3258, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p6394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6394 : lratChecker f6394 p6394 = .success := by decide +kernel
theorem unsat6394 : Unsatisfiable (PosFin 65) f6394 := by
  apply lratCheckerSound f6394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6394
  · intro a ha; simp [p6394] at ha; subst a; trivial
  · exact checked6394
theorem derived6394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6394 := by
  apply localUnsat_implies_entails f6394 [c2834, c2841, c2844, c3258] c6394 unsat6394 (by rfl) a
  have h0 : Entails.eval a c2834 := h 2833 (by decide)
  have h1 : Entails.eval a c2841 := h 2840 (by decide)
  have h2 : Entails.eval a c2844 := h 2843 (by decide)
  have h3 : Entails.eval a c3258 := h 3257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6395 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6393, some c4839, some c3429, some c6392, some c6227, some c6379, some c6380, some c4599, some c4600, some c4613, some c4615, some c5834, some c5213, some c4607, some c4350, some c5607, some c4022, some c4551, some c4362, some c6394, some c6384, some c6381, some c6387, some c3221, some c6386, some c3314, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked6395 : lratChecker f6395 p6395 = .success := by decide +kernel
theorem unsat6395 : Unsatisfiable (PosFin 65) f6395 := by
  apply lratCheckerSound f6395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6395
  · intro a ha; simp [p6395] at ha; subst a; trivial
  · exact checked6395
theorem derived6395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6395 := by
  apply localUnsat_implies_entails f6395 [c6393, c4839, c3429, c6392, c6227, c6379, c6380, c4599, c4600, c4613, c4615, c5834, c5213, c4607, c4350, c5607, c4022, c4551, c4362, c6394, c6384, c6381, c6387, c3221, c6386, c3314] c6395 unsat6395 (by rfl) a
  have h0 : Entails.eval a c6393 := derived6393 a h
  have h1 : Entails.eval a c4839 := h 4838 (by decide)
  have h2 : Entails.eval a c3429 := h 3428 (by decide)
  have h3 : Entails.eval a c6392 := derived6392 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6379 := derived6379 a h
  have h6 : Entails.eval a c6380 := derived6380 a h
  have h7 : Entails.eval a c4599 := h 4598 (by decide)
  have h8 : Entails.eval a c4600 := h 4599 (by decide)
  have h9 : Entails.eval a c4613 := h 4612 (by decide)
  have h10 : Entails.eval a c4615 := h 4614 (by decide)
  have h11 : Entails.eval a c5834 := h 5833 (by decide)
  have h12 : Entails.eval a c5213 := h 5212 (by decide)
  have h13 : Entails.eval a c4607 := h 4606 (by decide)
  have h14 : Entails.eval a c4350 := h 4349 (by decide)
  have h15 : Entails.eval a c5607 := h 5606 (by decide)
  have h16 : Entails.eval a c4022 := h 4021 (by decide)
  have h17 : Entails.eval a c4551 := h 4550 (by decide)
  have h18 : Entails.eval a c4362 := h 4361 (by decide)
  have h19 : Entails.eval a c6394 := derived6394 a h
  have h20 : Entails.eval a c6384 := derived6384 a h
  have h21 : Entails.eval a c6381 := derived6381 a h
  have h22 : Entails.eval a c6387 := derived6387 a h
  have h23 : Entails.eval a c3221 := h 3220 (by decide)
  have h24 : Entails.eval a c6386 := derived6386 a h
  have h25 : Entails.eval a c3314 := h 3313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6396 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6393, some c6392, some c6227, some c4839, some c6395, some c4356, some c5736, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6396 : lratChecker f6396 p6396 = .success := by decide +kernel
theorem unsat6396 : Unsatisfiable (PosFin 65) f6396 := by
  apply lratCheckerSound f6396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6396
  · intro a ha; simp [p6396] at ha; subst a; trivial
  · exact checked6396
theorem derived6396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6396 := by
  apply localUnsat_implies_entails f6396 [c6393, c6392, c6227, c4839, c6395, c4356, c5736] c6396 unsat6396 (by rfl) a
  have h0 : Entails.eval a c6393 := derived6393 a h
  have h1 : Entails.eval a c6392 := derived6392 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c4839 := h 4838 (by decide)
  have h4 : Entails.eval a c6395 := derived6395 a h
  have h5 : Entails.eval a c4356 := h 4355 (by decide)
  have h6 : Entails.eval a c5736 := h 5735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6397 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨59, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2973, some c3022, some c2784, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p6397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6397 : lratChecker f6397 p6397 = .success := by decide +kernel
theorem unsat6397 : Unsatisfiable (PosFin 65) f6397 := by
  apply lratCheckerSound f6397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6397
  · intro a ha; simp [p6397] at ha; subst a; trivial
  · exact checked6397
theorem derived6397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6397 := by
  apply localUnsat_implies_entails f6397 [c2973, c3022, c2784] c6397 unsat6397 (by rfl) a
  have h0 : Entails.eval a c2973 := h 2972 (by decide)
  have h1 : Entails.eval a c3022 := h 3021 (by decide)
  have h2 : Entails.eval a c2784 := h 2783 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6398 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6393, some c6371, some c6227, some c6392, some c6396, some c4837, some c5742, some c3426, some c4356, some c4600, some c4613, some c5184, some c4599, some c3564, some c4023, some c4944, some c4049, some c4350, some c3566, some c4595, some c5604, some c3521, some c6389, some c6391, some c6397, some c2834, some c2844, some c3257, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked6398 : lratChecker f6398 p6398 = .success := by decide +kernel
theorem unsat6398 : Unsatisfiable (PosFin 65) f6398 := by
  apply lratCheckerSound f6398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6398
  · intro a ha; simp [p6398] at ha; subst a; trivial
  · exact checked6398
theorem derived6398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6398 := by
  apply localUnsat_implies_entails f6398 [c6393, c6371, c6227, c6392, c6396, c4837, c5742, c3426, c4356, c4600, c4613, c5184, c4599, c3564, c4023, c4944, c4049, c4350, c3566, c4595, c5604, c3521, c6389, c6391, c6397, c2834, c2844, c3257] c6398 unsat6398 (by rfl) a
  have h0 : Entails.eval a c6393 := derived6393 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6392 := derived6392 a h
  have h4 : Entails.eval a c6396 := derived6396 a h
  have h5 : Entails.eval a c4837 := h 4836 (by decide)
  have h6 : Entails.eval a c5742 := h 5741 (by decide)
  have h7 : Entails.eval a c3426 := h 3425 (by decide)
  have h8 : Entails.eval a c4356 := h 4355 (by decide)
  have h9 : Entails.eval a c4600 := h 4599 (by decide)
  have h10 : Entails.eval a c4613 := h 4612 (by decide)
  have h11 : Entails.eval a c5184 := h 5183 (by decide)
  have h12 : Entails.eval a c4599 := h 4598 (by decide)
  have h13 : Entails.eval a c3564 := h 3563 (by decide)
  have h14 : Entails.eval a c4023 := h 4022 (by decide)
  have h15 : Entails.eval a c4944 := h 4943 (by decide)
  have h16 : Entails.eval a c4049 := h 4048 (by decide)
  have h17 : Entails.eval a c4350 := h 4349 (by decide)
  have h18 : Entails.eval a c3566 := h 3565 (by decide)
  have h19 : Entails.eval a c4595 := h 4594 (by decide)
  have h20 : Entails.eval a c5604 := h 5603 (by decide)
  have h21 : Entails.eval a c3521 := h 3520 (by decide)
  have h22 : Entails.eval a c6389 := derived6389 a h
  have h23 : Entails.eval a c6391 := derived6391 a h
  have h24 : Entails.eval a c6397 := derived6397 a h
  have h25 : Entails.eval a c2834 := h 2833 (by decide)
  have h26 : Entails.eval a c2844 := h 2843 (by decide)
  have h27 : Entails.eval a c3257 := h 3256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6399 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6398, some c3872, some c3868, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6399 : lratChecker f6399 p6399 = .success := by decide +kernel
theorem unsat6399 : Unsatisfiable (PosFin 65) f6399 := by
  apply lratCheckerSound f6399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6399
  · intro a ha; simp [p6399] at ha; subst a; trivial
  · exact checked6399
theorem derived6399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6399 := by
  apply localUnsat_implies_entails f6399 [c6227, c6398, c3872, c3868] c6399 unsat6399 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6398 := derived6398 a h
  have h2 : Entails.eval a c3872 := h 3871 (by decide)
  have h3 : Entails.eval a c3868 := h 3867 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6400 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6399, some c6227, some c3881, some c3872, some c3873, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6400 : lratChecker f6400 p6400 = .success := by decide +kernel
theorem unsat6400 : Unsatisfiable (PosFin 65) f6400 := by
  apply lratCheckerSound f6400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6400
  · intro a ha; simp [p6400] at ha; subst a; trivial
  · exact checked6400
theorem derived6400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6400 := by
  apply localUnsat_implies_entails f6400 [c6399, c6227, c3881, c3872, c3873] c6400 unsat6400 (by rfl) a
  have h0 : Entails.eval a c6399 := derived6399 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c3881 := h 3880 (by decide)
  have h3 : Entails.eval a c3872 := h 3871 (by decide)
  have h4 : Entails.eval a c3873 := h 3872 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6401 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c3833, some c5744, some c4840, some c3430, some c5187, some c5845, some c4021, some c5215, some c5606, some c5382, some c6130, some c3960, some c4506, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6401 : lratChecker f6401 p6401 = .success := by decide +kernel
theorem unsat6401 : Unsatisfiable (PosFin 65) f6401 := by
  apply lratCheckerSound f6401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6401
  · intro a ha; simp [p6401] at ha; subst a; trivial
  · exact checked6401
theorem derived6401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6401 := by
  apply localUnsat_implies_entails f6401 [c6371, c6227, c3833, c5744, c4840, c3430, c5187, c5845, c4021, c5215, c5606, c5382, c6130, c3960, c4506] c6401 unsat6401 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c3833 := h 3832 (by decide)
  have h3 : Entails.eval a c5744 := h 5743 (by decide)
  have h4 : Entails.eval a c4840 := h 4839 (by decide)
  have h5 : Entails.eval a c3430 := h 3429 (by decide)
  have h6 : Entails.eval a c5187 := h 5186 (by decide)
  have h7 : Entails.eval a c5845 := h 5844 (by decide)
  have h8 : Entails.eval a c4021 := h 4020 (by decide)
  have h9 : Entails.eval a c5215 := h 5214 (by decide)
  have h10 : Entails.eval a c5606 := h 5605 (by decide)
  have h11 : Entails.eval a c5382 := h 5381 (by decide)
  have h12 : Entails.eval a c6130 := derived6130 a h
  have h13 : Entails.eval a c3960 := h 3959 (by decide)
  have h14 : Entails.eval a c4506 := h 4505 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6402 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3570, some c3843, some c4524, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6402 : lratChecker f6402 p6402 = .success := by decide +kernel
theorem unsat6402 : Unsatisfiable (PosFin 65) f6402 := by
  apply lratCheckerSound f6402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6402
  · intro a ha; simp [p6402] at ha; subst a; trivial
  · exact checked6402
theorem derived6402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6402 := by
  apply localUnsat_implies_entails f6402 [c3570, c3843, c4524] c6402 unsat6402 (by rfl) a
  have h0 : Entails.eval a c3570 := h 3569 (by decide)
  have h1 : Entails.eval a c3843 := h 3842 (by decide)
  have h2 : Entails.eval a c4524 := h 4523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6403 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c4523, some c4527, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6403 : lratChecker f6403 p6403 = .success := by decide +kernel
theorem unsat6403 : Unsatisfiable (PosFin 65) f6403 := by
  apply lratCheckerSound f6403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6403
  · intro a ha; simp [p6403] at ha; subst a; trivial
  · exact checked6403
theorem derived6403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6403 := by
  apply localUnsat_implies_entails f6403 [c6371, c4523, c4527] c6403 unsat6403 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c4523 := h 4522 (by decide)
  have h2 : Entails.eval a c4527 := h 4526 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6404 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6399, some c6400, some c6402, some c6401, some c3835, some c4839, some c6403, some c3514, some c3521, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6404 : lratChecker f6404 p6404 = .success := by decide +kernel
theorem unsat6404 : Unsatisfiable (PosFin 65) f6404 := by
  apply lratCheckerSound f6404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6404
  · intro a ha; simp [p6404] at ha; subst a; trivial
  · exact checked6404
theorem derived6404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6404 := by
  apply localUnsat_implies_entails f6404 [c6371, c6399, c6400, c6402, c6401, c3835, c4839, c6403, c3514, c3521] c6404 unsat6404 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6399 := derived6399 a h
  have h2 : Entails.eval a c6400 := derived6400 a h
  have h3 : Entails.eval a c6402 := derived6402 a h
  have h4 : Entails.eval a c6401 := derived6401 a h
  have h5 : Entails.eval a c3835 := h 3834 (by decide)
  have h6 : Entails.eval a c4839 := h 4838 (by decide)
  have h7 : Entails.eval a c6403 := derived6403 a h
  have h8 : Entails.eval a c3514 := h 3513 (by decide)
  have h9 : Entails.eval a c3521 := h 3520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6405 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨61, by decide⟩, true), (⟨44, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4373, some c5750, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p6405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6405 : lratChecker f6405 p6405 = .success := by decide +kernel
theorem unsat6405 : Unsatisfiable (PosFin 65) f6405 := by
  apply lratCheckerSound f6405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6405
  · intro a ha; simp [p6405] at ha; subst a; trivial
  · exact checked6405
theorem derived6405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6405 := by
  apply localUnsat_implies_entails f6405 [c4373, c5750] c6405 unsat6405 (by rfl) a
  have h0 : Entails.eval a c4373 := h 4372 (by decide)
  have h1 : Entails.eval a c5750 := h 5749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6406 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨61, by decide⟩, true), (⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6371, some c6227, some c6403, some c4839, some c6405, some c4345, some c5213, some c5557, some c5064, some c4961, some c3741, some c3649, some c5883, some c4136, some c6291, some c4318, some c4892, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6406 : lratChecker f6406 p6406 = .success := by decide +kernel
theorem unsat6406 : Unsatisfiable (PosFin 65) f6406 := by
  apply lratCheckerSound f6406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6406
  · intro a ha; simp [p6406] at ha; subst a; trivial
  · exact checked6406
theorem derived6406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6406 := by
  apply localUnsat_implies_entails f6406 [c6404, c6371, c6227, c6403, c4839, c6405, c4345, c5213, c5557, c5064, c4961, c3741, c3649, c5883, c4136, c6291, c4318, c4892] c6406 unsat6406 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6403 := derived6403 a h
  have h4 : Entails.eval a c4839 := h 4838 (by decide)
  have h5 : Entails.eval a c6405 := derived6405 a h
  have h6 : Entails.eval a c4345 := h 4344 (by decide)
  have h7 : Entails.eval a c5213 := h 5212 (by decide)
  have h8 : Entails.eval a c5557 := h 5556 (by decide)
  have h9 : Entails.eval a c5064 := h 5063 (by decide)
  have h10 : Entails.eval a c4961 := h 4960 (by decide)
  have h11 : Entails.eval a c3741 := h 3740 (by decide)
  have h12 : Entails.eval a c3649 := h 3648 (by decide)
  have h13 : Entails.eval a c5883 := derived5883 a h
  have h14 : Entails.eval a c4136 := h 4135 (by decide)
  have h15 : Entails.eval a c6291 := derived6291 a h
  have h16 : Entails.eval a c4318 := h 4317 (by decide)
  have h17 : Entails.eval a c4892 := h 4891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6407 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3585, some c3613, some c4678, some c4923, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6407 : lratChecker f6407 p6407 = .success := by decide +kernel
theorem unsat6407 : Unsatisfiable (PosFin 65) f6407 := by
  apply lratCheckerSound f6407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6407
  · intro a ha; simp [p6407] at ha; subst a; trivial
  · exact checked6407
theorem derived6407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6407 := by
  apply localUnsat_implies_entails f6407 [c3585, c3613, c4678, c4923] c6407 unsat6407 (by rfl) a
  have h0 : Entails.eval a c3585 := h 3584 (by decide)
  have h1 : Entails.eval a c3613 := h 3612 (by decide)
  have h2 : Entails.eval a c4678 := h 4677 (by decide)
  have h3 : Entails.eval a c4923 := h 4922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6408 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6227, some c6407, some c5121, some c5064, some c4839, some c6406, some c3741, some c3682, some c4524, some c4923, some c5288, some c6292, some c4003, some c3641, some c6291, some c4318, some c4892, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6408 : lratChecker f6408 p6408 = .success := by decide +kernel
theorem unsat6408 : Unsatisfiable (PosFin 65) f6408 := by
  apply lratCheckerSound f6408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6408
  · intro a ha; simp [p6408] at ha; subst a; trivial
  · exact checked6408
theorem derived6408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6408 := by
  apply localUnsat_implies_entails f6408 [c6404, c6227, c6407, c5121, c5064, c4839, c6406, c3741, c3682, c4524, c4923, c5288, c6292, c4003, c3641, c6291, c4318, c4892] c6408 unsat6408 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6407 := derived6407 a h
  have h3 : Entails.eval a c5121 := h 5120 (by decide)
  have h4 : Entails.eval a c5064 := h 5063 (by decide)
  have h5 : Entails.eval a c4839 := h 4838 (by decide)
  have h6 : Entails.eval a c6406 := derived6406 a h
  have h7 : Entails.eval a c3741 := h 3740 (by decide)
  have h8 : Entails.eval a c3682 := h 3681 (by decide)
  have h9 : Entails.eval a c4524 := h 4523 (by decide)
  have h10 : Entails.eval a c4923 := h 4922 (by decide)
  have h11 : Entails.eval a c5288 := h 5287 (by decide)
  have h12 : Entails.eval a c6292 := derived6292 a h
  have h13 : Entails.eval a c4003 := h 4002 (by decide)
  have h14 : Entails.eval a c3641 := h 3640 (by decide)
  have h15 : Entails.eval a c6291 := derived6291 a h
  have h16 : Entails.eval a c4318 := h 4317 (by decide)
  have h17 : Entails.eval a c4892 := h 4891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6409 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨47, by decide⟩, false), (⟨46, by decide⟩, true), (⟨37, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6227, some c4524, some c5566, some c5293, some c6292, some c6291, some c6376, some c5851, some c5862, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6409 : lratChecker f6409 p6409 = .success := by decide +kernel
theorem unsat6409 : Unsatisfiable (PosFin 65) f6409 := by
  apply lratCheckerSound f6409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6409
  · intro a ha; simp [p6409] at ha; subst a; trivial
  · exact checked6409
theorem derived6409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6409 := by
  apply localUnsat_implies_entails f6409 [c6404, c6227, c4524, c5566, c5293, c6292, c6291, c6376, c5851, c5862] c6409 unsat6409 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4524 := h 4523 (by decide)
  have h3 : Entails.eval a c5566 := h 5565 (by decide)
  have h4 : Entails.eval a c5293 := h 5292 (by decide)
  have h5 : Entails.eval a c6292 := derived6292 a h
  have h6 : Entails.eval a c6291 := derived6291 a h
  have h7 : Entails.eval a c6376 := derived6376 a h
  have h8 : Entails.eval a c5851 := h 5850 (by decide)
  have h9 : Entails.eval a c5862 := h 5861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6410 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨37, by decide⟩, false), (⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c5744, some c5187, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6410 : lratChecker f6410 p6410 = .success := by decide +kernel
theorem unsat6410 : Unsatisfiable (PosFin 65) f6410 := by
  apply lratCheckerSound f6410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6410
  · intro a ha; simp [p6410] at ha; subst a; trivial
  · exact checked6410
theorem derived6410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6410 := by
  apply localUnsat_implies_entails f6410 [c6371, c6227, c5744, c5187] c6410 unsat6410 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5744 := h 5743 (by decide)
  have h3 : Entails.eval a c5187 := h 5186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6411 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6408, some c6404, some c6410, some c4524, some c4485, some c3751, some c4346, some c6409, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6411 : lratChecker f6411 p6411 = .success := by decide +kernel
theorem unsat6411 : Unsatisfiable (PosFin 65) f6411 := by
  apply lratCheckerSound f6411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6411
  · intro a ha; simp [p6411] at ha; subst a; trivial
  · exact checked6411
theorem derived6411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6411 := by
  apply localUnsat_implies_entails f6411 [c6408, c6404, c6410, c4524, c4485, c3751, c4346, c6409] c6411 unsat6411 (by rfl) a
  have h0 : Entails.eval a c6408 := derived6408 a h
  have h1 : Entails.eval a c6404 := derived6404 a h
  have h2 : Entails.eval a c6410 := derived6410 a h
  have h3 : Entails.eval a c4524 := h 4523 (by decide)
  have h4 : Entails.eval a c4485 := h 4484 (by decide)
  have h5 : Entails.eval a c3751 := h 3750 (by decide)
  have h6 : Entails.eval a c4346 := h 4345 (by decide)
  have h7 : Entails.eval a c6409 := derived6409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6412 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c5212, some c3586, some c3583, some c5221, some c5877, some c4524, some c4618, some c4608, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6412 : lratChecker f6412 p6412 = .success := by decide +kernel
theorem unsat6412 : Unsatisfiable (PosFin 65) f6412 := by
  apply lratCheckerSound f6412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6412
  · intro a ha; simp [p6412] at ha; subst a; trivial
  · exact checked6412
theorem derived6412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6412 := by
  apply localUnsat_implies_entails f6412 [c6371, c6227, c5212, c3586, c3583, c5221, c5877, c4524, c4618, c4608] c6412 unsat6412 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5212 := h 5211 (by decide)
  have h3 : Entails.eval a c3586 := h 3585 (by decide)
  have h4 : Entails.eval a c3583 := h 3582 (by decide)
  have h5 : Entails.eval a c5221 := h 5220 (by decide)
  have h6 : Entails.eval a c5877 := h 5876 (by decide)
  have h7 : Entails.eval a c4524 := h 4523 (by decide)
  have h8 : Entails.eval a c4618 := h 4617 (by decide)
  have h9 : Entails.eval a c4608 := h 4607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6413 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4524, some c4346, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6413 : lratChecker f6413 p6413 = .success := by decide +kernel
theorem unsat6413 : Unsatisfiable (PosFin 65) f6413 := by
  apply lratCheckerSound f6413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6413
  · intro a ha; simp [p6413] at ha; subst a; trivial
  · exact checked6413
theorem derived6413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6413 := by
  apply localUnsat_implies_entails f6413 [c4524, c4346] c6413 unsat6413 (by rfl) a
  have h0 : Entails.eval a c4524 := h 4523 (by decide)
  have h1 : Entails.eval a c4346 := h 4345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6414 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6408, some c6404, some c6371, some c6411, some c6412, some c6413, some c3610, some c5744, some c5845, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6414 : lratChecker f6414 p6414 = .success := by decide +kernel
theorem unsat6414 : Unsatisfiable (PosFin 65) f6414 := by
  apply lratCheckerSound f6414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6414
  · intro a ha; simp [p6414] at ha; subst a; trivial
  · exact checked6414
theorem derived6414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6414 := by
  apply localUnsat_implies_entails f6414 [c6408, c6404, c6371, c6411, c6412, c6413, c3610, c5744, c5845] c6414 unsat6414 (by rfl) a
  have h0 : Entails.eval a c6408 := derived6408 a h
  have h1 : Entails.eval a c6404 := derived6404 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6411 := derived6411 a h
  have h4 : Entails.eval a c6412 := derived6412 a h
  have h5 : Entails.eval a c6413 := derived6413 a h
  have h6 : Entails.eval a c3610 := h 3609 (by decide)
  have h7 : Entails.eval a c5744 := h 5743 (by decide)
  have h8 : Entails.eval a c5845 := h 5844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6415 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6408, some c6371, some c6414, some c4838, some c4844, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6415 : lratChecker f6415 p6415 = .success := by decide +kernel
theorem unsat6415 : Unsatisfiable (PosFin 65) f6415 := by
  apply lratCheckerSound f6415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6415
  · intro a ha; simp [p6415] at ha; subst a; trivial
  · exact checked6415
theorem derived6415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6415 := by
  apply localUnsat_implies_entails f6415 [c6408, c6371, c6414, c4838, c4844] c6415 unsat6415 (by rfl) a
  have h0 : Entails.eval a c6408 := derived6408 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6414 := derived6414 a h
  have h3 : Entails.eval a c4838 := h 4837 (by decide)
  have h4 : Entails.eval a c4844 := h 4843 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6416 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨61, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c4676, some c4047, some c3593, some c3604, some c4672, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6416 : lratChecker f6416 p6416 = .success := by decide +kernel
theorem unsat6416 : Unsatisfiable (PosFin 65) f6416 := by
  apply lratCheckerSound f6416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6416
  · intro a ha; simp [p6416] at ha; subst a; trivial
  · exact checked6416
theorem derived6416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6416 := by
  apply localUnsat_implies_entails f6416 [c6371, c6227, c4676, c4047, c3593, c3604, c4672] c6416 unsat6416 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4676 := h 4675 (by decide)
  have h3 : Entails.eval a c4047 := h 4046 (by decide)
  have h4 : Entails.eval a c3593 := h 3592 (by decide)
  have h5 : Entails.eval a c3604 := h 3603 (by decide)
  have h6 : Entails.eval a c4672 := h 4671 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6417 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨36, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6415, some c6408, some c6404, some c6371, some c4777, some c4121, some c5474, some c4166, some c4485, some c3961, some c5334, some c5293, some c6416, some c5118, some c5010, some c5057, some c5054, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6417 : lratChecker f6417 p6417 = .success := by decide +kernel
theorem unsat6417 : Unsatisfiable (PosFin 65) f6417 := by
  apply lratCheckerSound f6417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6417
  · intro a ha; simp [p6417] at ha; subst a; trivial
  · exact checked6417
theorem derived6417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6417 := by
  apply localUnsat_implies_entails f6417 [c6415, c6408, c6404, c6371, c4777, c4121, c5474, c4166, c4485, c3961, c5334, c5293, c6416, c5118, c5010, c5057, c5054] c6417 unsat6417 (by rfl) a
  have h0 : Entails.eval a c6415 := derived6415 a h
  have h1 : Entails.eval a c6408 := derived6408 a h
  have h2 : Entails.eval a c6404 := derived6404 a h
  have h3 : Entails.eval a c6371 := derived6371 a h
  have h4 : Entails.eval a c4777 := h 4776 (by decide)
  have h5 : Entails.eval a c4121 := h 4120 (by decide)
  have h6 : Entails.eval a c5474 := h 5473 (by decide)
  have h7 : Entails.eval a c4166 := h 4165 (by decide)
  have h8 : Entails.eval a c4485 := h 4484 (by decide)
  have h9 : Entails.eval a c3961 := h 3960 (by decide)
  have h10 : Entails.eval a c5334 := h 5333 (by decide)
  have h11 : Entails.eval a c5293 := h 5292 (by decide)
  have h12 : Entails.eval a c6416 := derived6416 a h
  have h13 : Entails.eval a c5118 := h 5117 (by decide)
  have h14 : Entails.eval a c5010 := h 5009 (by decide)
  have h15 : Entails.eval a c5057 := h 5056 (by decide)
  have h16 : Entails.eval a c5054 := h 5053 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6418 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6415, some c6408, some c6371, some c6227, some c6417, some c5119, some c4679, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6418 : lratChecker f6418 p6418 = .success := by decide +kernel
theorem unsat6418 : Unsatisfiable (PosFin 65) f6418 := by
  apply lratCheckerSound f6418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6418
  · intro a ha; simp [p6418] at ha; subst a; trivial
  · exact checked6418
theorem derived6418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6418 := by
  apply localUnsat_implies_entails f6418 [c6415, c6408, c6371, c6227, c6417, c5119, c4679] c6418 unsat6418 (by rfl) a
  have h0 : Entails.eval a c6415 := derived6415 a h
  have h1 : Entails.eval a c6408 := derived6408 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6417 := derived6417 a h
  have h5 : Entails.eval a c5119 := h 5118 (by decide)
  have h6 : Entails.eval a c4679 := h 4678 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6419 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c5119, some c5215, some c4920, some c3610, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6419 : lratChecker f6419 p6419 = .success := by decide +kernel
theorem unsat6419 : Unsatisfiable (PosFin 65) f6419 := by
  apply lratCheckerSound f6419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6419
  · intro a ha; simp [p6419] at ha; subst a; trivial
  · exact checked6419
theorem derived6419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6419 := by
  apply localUnsat_implies_entails f6419 [c6371, c6227, c5119, c5215, c4920, c3610] c6419 unsat6419 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5119 := h 5118 (by decide)
  have h3 : Entails.eval a c5215 := h 5214 (by decide)
  have h4 : Entails.eval a c4920 := h 4919 (by decide)
  have h5 : Entails.eval a c3610 := h 3609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6420 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c5732, some c4346, some c4925, some c5169, some c4450, some c3609, some c4388, some c4387, some c4121, some c4033, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6420 : lratChecker f6420 p6420 = .success := by decide +kernel
theorem unsat6420 : Unsatisfiable (PosFin 65) f6420 := by
  apply lratCheckerSound f6420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6420
  · intro a ha; simp [p6420] at ha; subst a; trivial
  · exact checked6420
theorem derived6420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6420 := by
  apply localUnsat_implies_entails f6420 [c6371, c5732, c4346, c4925, c5169, c4450, c3609, c4388, c4387, c4121, c4033] c6420 unsat6420 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c5732 := h 5731 (by decide)
  have h2 : Entails.eval a c4346 := h 4345 (by decide)
  have h3 : Entails.eval a c4925 := h 4924 (by decide)
  have h4 : Entails.eval a c5169 := h 5168 (by decide)
  have h5 : Entails.eval a c4450 := h 4449 (by decide)
  have h6 : Entails.eval a c3609 := h 3608 (by decide)
  have h7 : Entails.eval a c4388 := h 4387 (by decide)
  have h8 : Entails.eval a c4387 := h 4386 (by decide)
  have h9 : Entails.eval a c4121 := h 4120 (by decide)
  have h10 : Entails.eval a c4033 := h 4032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6421 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6420, some c3583, some c5221, some c3599, some c3587, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6421 : lratChecker f6421 p6421 = .success := by decide +kernel
theorem unsat6421 : Unsatisfiable (PosFin 65) f6421 := by
  apply lratCheckerSound f6421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6421
  · intro a ha; simp [p6421] at ha; subst a; trivial
  · exact checked6421
theorem derived6421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6421 := by
  apply localUnsat_implies_entails f6421 [c6371, c6420, c3583, c5221, c3599, c3587] c6421 unsat6421 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6420 := derived6420 a h
  have h2 : Entails.eval a c3583 := h 3582 (by decide)
  have h3 : Entails.eval a c5221 := h 5220 (by decide)
  have h4 : Entails.eval a c3599 := h 3598 (by decide)
  have h5 : Entails.eval a c3587 := h 3586 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6422 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6371, some c6408, some c6415, some c6418, some c6419, some c6421, some c5118, some c5125, some c5131, some c5122, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6422 : lratChecker f6422 p6422 = .success := by decide +kernel
theorem unsat6422 : Unsatisfiable (PosFin 65) f6422 := by
  apply lratCheckerSound f6422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6422
  · intro a ha; simp [p6422] at ha; subst a; trivial
  · exact checked6422
theorem derived6422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6422 := by
  apply localUnsat_implies_entails f6422 [c6404, c6371, c6408, c6415, c6418, c6419, c6421, c5118, c5125, c5131, c5122] c6422 unsat6422 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6408 := derived6408 a h
  have h3 : Entails.eval a c6415 := derived6415 a h
  have h4 : Entails.eval a c6418 := derived6418 a h
  have h5 : Entails.eval a c6419 := derived6419 a h
  have h6 : Entails.eval a c6421 := derived6421 a h
  have h7 : Entails.eval a c5118 := h 5117 (by decide)
  have h8 : Entails.eval a c5125 := h 5124 (by decide)
  have h9 : Entails.eval a c5131 := h 5130 (by decide)
  have h10 : Entails.eval a c5122 := h 5121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6423 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5681, some c5826, some c3751, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6423 : lratChecker f6423 p6423 = .success := by decide +kernel
theorem unsat6423 : Unsatisfiable (PosFin 65) f6423 := by
  apply lratCheckerSound f6423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6423
  · intro a ha; simp [p6423] at ha; subst a; trivial
  · exact checked6423
theorem derived6423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6423 := by
  apply localUnsat_implies_entails f6423 [c5681, c5826, c3751] c6423 unsat6423 (by rfl) a
  have h0 : Entails.eval a c5681 := h 5680 (by decide)
  have h1 : Entails.eval a c5826 := h 5825 (by decide)
  have h2 : Entails.eval a c3751 := h 3750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6424 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨47, by decide⟩, true), (⟨61, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c3749, some c3755, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6424 : lratChecker f6424 p6424 = .success := by decide +kernel
theorem unsat6424 : Unsatisfiable (PosFin 65) f6424 := by
  apply lratCheckerSound f6424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6424
  · intro a ha; simp [p6424] at ha; subst a; trivial
  · exact checked6424
theorem derived6424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6424 := by
  apply localUnsat_implies_entails f6424 [c6371, c3749, c3755] c6424 unsat6424 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c3749 := h 3748 (by decide)
  have h2 : Entails.eval a c3755 := h 3754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6425 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6422, some c6423, some c6227, some c5678, some c5677, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6425 : lratChecker f6425 p6425 = .success := by decide +kernel
theorem unsat6425 : Unsatisfiable (PosFin 65) f6425 := by
  apply lratCheckerSound f6425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6425
  · intro a ha; simp [p6425] at ha; subst a; trivial
  · exact checked6425
theorem derived6425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6425 := by
  apply localUnsat_implies_entails f6425 [c6404, c6422, c6423, c6227, c5678, c5677] c6425 unsat6425 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6422 := derived6422 a h
  have h2 : Entails.eval a c6423 := derived6423 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c5678 := h 5677 (by decide)
  have h5 : Entails.eval a c5677 := h 5676 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6426 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6371, some c6422, some c6423, some c6425, some c6424, some c5819, some c5817, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6426 : lratChecker f6426 p6426 = .success := by decide +kernel
theorem unsat6426 : Unsatisfiable (PosFin 65) f6426 := by
  apply lratCheckerSound f6426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6426
  · intro a ha; simp [p6426] at ha; subst a; trivial
  · exact checked6426
theorem derived6426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6426 := by
  apply localUnsat_implies_entails f6426 [c6404, c6371, c6422, c6423, c6425, c6424, c5819, c5817] c6426 unsat6426 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6422 := derived6422 a h
  have h3 : Entails.eval a c6423 := derived6423 a h
  have h4 : Entails.eval a c6425 := derived6425 a h
  have h5 : Entails.eval a c6424 := derived6424 a h
  have h6 : Entails.eval a c5819 := h 5818 (by decide)
  have h7 : Entails.eval a c5817 := h 5816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6427 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨61, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c5819, some c5817, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6427 : lratChecker f6427 p6427 = .success := by decide +kernel
theorem unsat6427 : Unsatisfiable (PosFin 65) f6427 := by
  apply lratCheckerSound f6427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6427
  · intro a ha; simp [p6427] at ha; subst a; trivial
  · exact checked6427
theorem derived6427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6427 := by
  apply localUnsat_implies_entails f6427 [c6371, c5819, c5817] c6427 unsat6427 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c5819 := h 5818 (by decide)
  have h2 : Entails.eval a c5817 := h 5816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6428 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨47, by decide⟩, true), (⟨61, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c5678, some c3739, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6428 : lratChecker f6428 p6428 = .success := by decide +kernel
theorem unsat6428 : Unsatisfiable (PosFin 65) f6428 := by
  apply lratCheckerSound f6428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6428
  · intro a ha; simp [p6428] at ha; subst a; trivial
  · exact checked6428
theorem derived6428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6428 := by
  apply localUnsat_implies_entails f6428 [c6371, c6227, c5678, c3739] c6428 unsat6428 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5678 := h 5677 (by decide)
  have h3 : Entails.eval a c3739 := h 3738 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6429 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c6427, some c6428, some c5677, some c3741, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6429 : lratChecker f6429 p6429 = .success := by decide +kernel
theorem unsat6429 : Unsatisfiable (PosFin 65) f6429 := by
  apply lratCheckerSound f6429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6429
  · intro a ha; simp [p6429] at ha; subst a; trivial
  · exact checked6429
theorem derived6429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6429 := by
  apply localUnsat_implies_entails f6429 [c6404, c6427, c6428, c5677, c3741] c6429 unsat6429 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c6427 := derived6427 a h
  have h2 : Entails.eval a c6428 := derived6428 a h
  have h3 : Entails.eval a c5677 := h 5676 (by decide)
  have h4 : Entails.eval a c3741 := h 3740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6430 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨47, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6404, some c5677, some c3741, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6430 : lratChecker f6430 p6430 = .success := by decide +kernel
theorem unsat6430 : Unsatisfiable (PosFin 65) f6430 := by
  apply lratCheckerSound f6430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6430
  · intro a ha; simp [p6430] at ha; subst a; trivial
  · exact checked6430
theorem derived6430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6430 := by
  apply localUnsat_implies_entails f6430 [c6404, c5677, c3741] c6430 unsat6430 (by rfl) a
  have h0 : Entails.eval a c6404 := derived6404 a h
  have h1 : Entails.eval a c5677 := h 5676 (by decide)
  have h2 : Entails.eval a c3741 := h 3740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6431 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6429, some c6426, some c6404, some c6227, some c6430, some c5675, some c3736, some c3730, some c3734, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6431 : lratChecker f6431 p6431 = .success := by decide +kernel
theorem unsat6431 : Unsatisfiable (PosFin 65) f6431 := by
  apply lratCheckerSound f6431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6431
  · intro a ha; simp [p6431] at ha; subst a; trivial
  · exact checked6431
theorem derived6431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6431 := by
  apply localUnsat_implies_entails f6431 [c6429, c6426, c6404, c6227, c6430, c5675, c3736, c3730, c3734] c6431 unsat6431 (by rfl) a
  have h0 : Entails.eval a c6429 := derived6429 a h
  have h1 : Entails.eval a c6426 := derived6426 a h
  have h2 : Entails.eval a c6404 := derived6404 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6430 := derived6430 a h
  have h5 : Entails.eval a c5675 := h 5674 (by decide)
  have h6 : Entails.eval a c3736 := h 3735 (by decide)
  have h7 : Entails.eval a c3730 := h 3729 (by decide)
  have h8 : Entails.eval a c3734 := h 3733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6432 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6426, some c6404, some c6371, some c6227, some c6429, some c6431, some c5819, some c5814, some c5822, some c5675, some c5815, some c5821, some c3769, some c3681, some c5490, some c5846, some c4822, some c4953, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6432 : lratChecker f6432 p6432 = .success := by decide +kernel
theorem unsat6432 : Unsatisfiable (PosFin 65) f6432 := by
  apply lratCheckerSound f6432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6432
  · intro a ha; simp [p6432] at ha; subst a; trivial
  · exact checked6432
theorem derived6432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6432 := by
  apply localUnsat_implies_entails f6432 [c6426, c6404, c6371, c6227, c6429, c6431, c5819, c5814, c5822, c5675, c5815, c5821, c3769, c3681, c5490, c5846, c4822, c4953] c6432 unsat6432 (by rfl) a
  have h0 : Entails.eval a c6426 := derived6426 a h
  have h1 : Entails.eval a c6404 := derived6404 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6429 := derived6429 a h
  have h5 : Entails.eval a c6431 := derived6431 a h
  have h6 : Entails.eval a c5819 := h 5818 (by decide)
  have h7 : Entails.eval a c5814 := h 5813 (by decide)
  have h8 : Entails.eval a c5822 := h 5821 (by decide)
  have h9 : Entails.eval a c5675 := h 5674 (by decide)
  have h10 : Entails.eval a c5815 := h 5814 (by decide)
  have h11 : Entails.eval a c5821 := h 5820 (by decide)
  have h12 : Entails.eval a c3769 := h 3768 (by decide)
  have h13 : Entails.eval a c3681 := h 3680 (by decide)
  have h14 : Entails.eval a c5490 := h 5489 (by decide)
  have h15 : Entails.eval a c5846 := h 5845 (by decide)
  have h16 : Entails.eval a c4822 := h 4821 (by decide)
  have h17 : Entails.eval a c4953 := h 4952 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6433 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5845, some c5844, some c5839, some c5841, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p6433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6433 : lratChecker f6433 p6433 = .success := by decide +kernel
theorem unsat6433 : Unsatisfiable (PosFin 65) f6433 := by
  apply lratCheckerSound f6433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6433
  · intro a ha; simp [p6433] at ha; subst a; trivial
  · exact checked6433
theorem derived6433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6433 := by
  apply localUnsat_implies_entails f6433 [c5845, c5844, c5839, c5841] c6433 unsat6433 (by rfl) a
  have h0 : Entails.eval a c5845 := h 5844 (by decide)
  have h1 : Entails.eval a c5844 := h 5843 (by decide)
  have h2 : Entails.eval a c5839 := h 5838 (by decide)
  have h3 : Entails.eval a c5841 := h 5840 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6434 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨33, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3912, some c3663, some c3769, some c5321, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6434 : lratChecker f6434 p6434 = .success := by decide +kernel
theorem unsat6434 : Unsatisfiable (PosFin 65) f6434 := by
  apply lratCheckerSound f6434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6434
  · intro a ha; simp [p6434] at ha; subst a; trivial
  · exact checked6434
theorem derived6434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6434 := by
  apply localUnsat_implies_entails f6434 [c3912, c3663, c3769, c5321] c6434 unsat6434 (by rfl) a
  have h0 : Entails.eval a c3912 := h 3911 (by decide)
  have h1 : Entails.eval a c3663 := h 3662 (by decide)
  have h2 : Entails.eval a c3769 := h 3768 (by decide)
  have h3 : Entails.eval a c5321 := h 5320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6435 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨33, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c6433, some c6434, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6435 : lratChecker f6435 p6435 = .success := by decide +kernel
theorem unsat6435 : Unsatisfiable (PosFin 65) f6435 := by
  apply lratCheckerSound f6435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6435
  · intro a ha; simp [p6435] at ha; subst a; trivial
  · exact checked6435
theorem derived6435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6435 := by
  apply localUnsat_implies_entails f6435 [c6371, c6227, c6433, c6434] c6435 unsat6435 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6433 := derived6433 a h
  have h3 : Entails.eval a c6434 := derived6434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6436 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6432, some c6426, some c6404, some c6227, some c6435, some c6407, some c5121, some c5064, some c4839, some c6380, some c6232, some c4001, some c5736, some c4153, some c5481, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6436 : lratChecker f6436 p6436 = .success := by decide +kernel
theorem unsat6436 : Unsatisfiable (PosFin 65) f6436 := by
  apply lratCheckerSound f6436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6436
  · intro a ha; simp [p6436] at ha; subst a; trivial
  · exact checked6436
theorem derived6436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6436 := by
  apply localUnsat_implies_entails f6436 [c6432, c6426, c6404, c6227, c6435, c6407, c5121, c5064, c4839, c6380, c6232, c4001, c5736, c4153, c5481] c6436 unsat6436 (by rfl) a
  have h0 : Entails.eval a c6432 := derived6432 a h
  have h1 : Entails.eval a c6426 := derived6426 a h
  have h2 : Entails.eval a c6404 := derived6404 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6435 := derived6435 a h
  have h5 : Entails.eval a c6407 := derived6407 a h
  have h6 : Entails.eval a c5121 := h 5120 (by decide)
  have h7 : Entails.eval a c5064 := h 5063 (by decide)
  have h8 : Entails.eval a c4839 := h 4838 (by decide)
  have h9 : Entails.eval a c6380 := derived6380 a h
  have h10 : Entails.eval a c6232 := derived6232 a h
  have h11 : Entails.eval a c4001 := h 4000 (by decide)
  have h12 : Entails.eval a c5736 := h 5735 (by decide)
  have h13 : Entails.eval a c4153 := h 4152 (by decide)
  have h14 : Entails.eval a c5481 := h 5480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6437 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6436, some c6432, some c6404, some c6407, some c3741, some c5064, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6437 : lratChecker f6437 p6437 = .success := by decide +kernel
theorem unsat6437 : Unsatisfiable (PosFin 65) f6437 := by
  apply lratCheckerSound f6437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6437
  · intro a ha; simp [p6437] at ha; subst a; trivial
  · exact checked6437
theorem derived6437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6437 := by
  apply localUnsat_implies_entails f6437 [c6436, c6432, c6404, c6407, c3741, c5064] c6437 unsat6437 (by rfl) a
  have h0 : Entails.eval a c6436 := derived6436 a h
  have h1 : Entails.eval a c6432 := derived6432 a h
  have h2 : Entails.eval a c6404 := derived6404 a h
  have h3 : Entails.eval a c6407 := derived6407 a h
  have h4 : Entails.eval a c3741 := h 3740 (by decide)
  have h5 : Entails.eval a c5064 := h 5063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6438 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5060, some c5061, some c5181, some c5193, some c5179, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p6438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6438 : lratChecker f6438 p6438 = .success := by decide +kernel
theorem unsat6438 : Unsatisfiable (PosFin 65) f6438 := by
  apply lratCheckerSound f6438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6438
  · intro a ha; simp [p6438] at ha; subst a; trivial
  · exact checked6438
theorem derived6438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6438 := by
  apply localUnsat_implies_entails f6438 [c5060, c5061, c5181, c5193, c5179] c6438 unsat6438 (by rfl) a
  have h0 : Entails.eval a c5060 := h 5059 (by decide)
  have h1 : Entails.eval a c5061 := h 5060 (by decide)
  have h2 : Entails.eval a c5181 := h 5180 (by decide)
  have h3 : Entails.eval a c5193 := h 5192 (by decide)
  have h4 : Entails.eval a c5179 := h 5178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6439 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c3610, some c3609, some c3622, some c3631, some c3616, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6439 : lratChecker f6439 p6439 = .success := by decide +kernel
theorem unsat6439 : Unsatisfiable (PosFin 65) f6439 := by
  apply lratCheckerSound f6439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6439
  · intro a ha; simp [p6439] at ha; subst a; trivial
  · exact checked6439
theorem derived6439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6439 := by
  apply localUnsat_implies_entails f6439 [c6371, c3610, c3609, c3622, c3631, c3616] c6439 unsat6439 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c3610 := h 3609 (by decide)
  have h2 : Entails.eval a c3609 := h 3608 (by decide)
  have h3 : Entails.eval a c3622 := h 3621 (by decide)
  have h4 : Entails.eval a c3631 := h 3630 (by decide)
  have h5 : Entails.eval a c3616 := h 3615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6440 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c6404, some c6426, some c6436, some c6437, some c6434, some c6439, some c5187, some c5184, some c6438, some c5181, some c3730, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6440 : lratChecker f6440 p6440 = .success := by decide +kernel
theorem unsat6440 : Unsatisfiable (PosFin 65) f6440 := by
  apply lratCheckerSound f6440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6440
  · intro a ha; simp [p6440] at ha; subst a; trivial
  · exact checked6440
theorem derived6440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6440 := by
  apply localUnsat_implies_entails f6440 [c6371, c6227, c6404, c6426, c6436, c6437, c6434, c6439, c5187, c5184, c6438, c5181, c3730] c6440 unsat6440 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6404 := derived6404 a h
  have h3 : Entails.eval a c6426 := derived6426 a h
  have h4 : Entails.eval a c6436 := derived6436 a h
  have h5 : Entails.eval a c6437 := derived6437 a h
  have h6 : Entails.eval a c6434 := derived6434 a h
  have h7 : Entails.eval a c6439 := derived6439 a h
  have h8 : Entails.eval a c5187 := h 5186 (by decide)
  have h9 : Entails.eval a c5184 := h 5183 (by decide)
  have h10 : Entails.eval a c6438 := derived6438 a h
  have h11 : Entails.eval a c5181 := h 5180 (by decide)
  have h12 : Entails.eval a c3730 := h 3729 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6441 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3751, some c3730, some c3734, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6441 : lratChecker f6441 p6441 = .success := by decide +kernel
theorem unsat6441 : Unsatisfiable (PosFin 65) f6441 := by
  apply lratCheckerSound f6441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6441
  · intro a ha; simp [p6441] at ha; subst a; trivial
  · exact checked6441
theorem derived6441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6441 := by
  apply localUnsat_implies_entails f6441 [c3751, c3730, c3734] c6441 unsat6441 (by rfl) a
  have h0 : Entails.eval a c3751 := h 3750 (by decide)
  have h1 : Entails.eval a c3730 := h 3729 (by decide)
  have h2 : Entails.eval a c3734 := h 3733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6442 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨47, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3681, some c5575, some c5580, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6442 : lratChecker f6442 p6442 = .success := by decide +kernel
theorem unsat6442 : Unsatisfiable (PosFin 65) f6442 := by
  apply lratCheckerSound f6442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6442
  · intro a ha; simp [p6442] at ha; subst a; trivial
  · exact checked6442
theorem derived6442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6442 := by
  apply localUnsat_implies_entails f6442 [c3681, c5575, c5580] c6442 unsat6442 (by rfl) a
  have h0 : Entails.eval a c3681 := h 3680 (by decide)
  have h1 : Entails.eval a c5575 := h 5574 (by decide)
  have h2 : Entails.eval a c5580 := h 5579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6443 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6441, some c6442, some c3693, some c5032, some c5590, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6443 : lratChecker f6443 p6443 = .success := by decide +kernel
theorem unsat6443 : Unsatisfiable (PosFin 65) f6443 := by
  apply lratCheckerSound f6443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6443
  · intro a ha; simp [p6443] at ha; subst a; trivial
  · exact checked6443
theorem derived6443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6443 := by
  apply localUnsat_implies_entails f6443 [c6227, c6441, c6442, c3693, c5032, c5590] c6443 unsat6443 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6441 := derived6441 a h
  have h2 : Entails.eval a c6442 := derived6442 a h
  have h3 : Entails.eval a c3693 := h 3692 (by decide)
  have h4 : Entails.eval a c5032 := h 5031 (by decide)
  have h5 : Entails.eval a c5590 := h 5589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6444 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c6443, some c5238, some c3738, some c3640, some c5783, some c4941, some c5442, some c6233, some c4257, some c5488, some c4143, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6444 : lratChecker f6444 p6444 = .success := by decide +kernel
theorem unsat6444 : Unsatisfiable (PosFin 65) f6444 := by
  apply lratCheckerSound f6444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6444
  · intro a ha; simp [p6444] at ha; subst a; trivial
  · exact checked6444
theorem derived6444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6444 := by
  apply localUnsat_implies_entails f6444 [c6371, c6227, c6443, c5238, c3738, c3640, c5783, c4941, c5442, c6233, c4257, c5488, c4143] c6444 unsat6444 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6443 := derived6443 a h
  have h3 : Entails.eval a c5238 := h 5237 (by decide)
  have h4 : Entails.eval a c3738 := h 3737 (by decide)
  have h5 : Entails.eval a c3640 := h 3639 (by decide)
  have h6 : Entails.eval a c5783 := h 5782 (by decide)
  have h7 : Entails.eval a c4941 := h 4940 (by decide)
  have h8 : Entails.eval a c5442 := h 5441 (by decide)
  have h9 : Entails.eval a c6233 := derived6233 a h
  have h10 : Entails.eval a c4257 := h 4256 (by decide)
  have h11 : Entails.eval a c5488 := h 5487 (by decide)
  have h12 : Entails.eval a c4143 := h 4142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6445 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6444, some c5034, some c3684, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6445 : lratChecker f6445 p6445 = .success := by decide +kernel
theorem unsat6445 : Unsatisfiable (PosFin 65) f6445 := by
  apply lratCheckerSound f6445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6445
  · intro a ha; simp [p6445] at ha; subst a; trivial
  · exact checked6445
theorem derived6445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6445 := by
  apply localUnsat_implies_entails f6445 [c6227, c6444, c5034, c3684] c6445 unsat6445 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6444 := derived6444 a h
  have h2 : Entails.eval a c5034 := h 5033 (by decide)
  have h3 : Entails.eval a c3684 := h 3683 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6446 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c6434, some c3771, some c3772, some c3782, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6446 : lratChecker f6446 p6446 = .success := by decide +kernel
theorem unsat6446 : Unsatisfiable (PosFin 65) f6446 := by
  apply lratCheckerSound f6446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6446
  · intro a ha; simp [p6446] at ha; subst a; trivial
  · exact checked6446
theorem derived6446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6446 := by
  apply localUnsat_implies_entails f6446 [c6371, c6227, c6434, c3771, c3772, c3782] c6446 unsat6446 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6434 := derived6434 a h
  have h3 : Entails.eval a c3771 := h 3770 (by decide)
  have h4 : Entails.eval a c3772 := h 3771 (by decide)
  have h5 : Entails.eval a c3782 := h 3781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6447 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨61, by decide⟩, false), (⟨47, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3693, some c4143, some c5293, some c4085, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6447 : lratChecker f6447 p6447 = .success := by decide +kernel
theorem unsat6447 : Unsatisfiable (PosFin 65) f6447 := by
  apply lratCheckerSound f6447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6447
  · intro a ha; simp [p6447] at ha; subst a; trivial
  · exact checked6447
theorem derived6447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6447 := by
  apply localUnsat_implies_entails f6447 [c3693, c4143, c5293, c4085] c6447 unsat6447 (by rfl) a
  have h0 : Entails.eval a c3693 := h 3692 (by decide)
  have h1 : Entails.eval a c4143 := h 4142 (by decide)
  have h2 : Entails.eval a c5293 := h 5292 (by decide)
  have h3 : Entails.eval a c4085 := h 4084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6448 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6446, some c6445, some c6439, some c6227, some c6447, some c3681, some c6442, some c5582, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6448 : lratChecker f6448 p6448 = .success := by decide +kernel
theorem unsat6448 : Unsatisfiable (PosFin 65) f6448 := by
  apply lratCheckerSound f6448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6448
  · intro a ha; simp [p6448] at ha; subst a; trivial
  · exact checked6448
theorem derived6448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6448 := by
  apply localUnsat_implies_entails f6448 [c6446, c6445, c6439, c6227, c6447, c3681, c6442, c5582] c6448 unsat6448 (by rfl) a
  have h0 : Entails.eval a c6446 := derived6446 a h
  have h1 : Entails.eval a c6445 := derived6445 a h
  have h2 : Entails.eval a c6439 := derived6439 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6447 := derived6447 a h
  have h5 : Entails.eval a c3681 := h 3680 (by decide)
  have h6 : Entails.eval a c6442 := derived6442 a h
  have h7 : Entails.eval a c5582 := h 5581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6449 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c6446, some c6445, some c6439, some c6448, some c3684, some c4942, some c5491, some c4820, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6449 : lratChecker f6449 p6449 = .success := by decide +kernel
theorem unsat6449 : Unsatisfiable (PosFin 65) f6449 := by
  apply lratCheckerSound f6449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6449
  · intro a ha; simp [p6449] at ha; subst a; trivial
  · exact checked6449
theorem derived6449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6449 := by
  apply localUnsat_implies_entails f6449 [c6371, c6227, c6446, c6445, c6439, c6448, c3684, c4942, c5491, c4820] c6449 unsat6449 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6446 := derived6446 a h
  have h3 : Entails.eval a c6445 := derived6445 a h
  have h4 : Entails.eval a c6439 := derived6439 a h
  have h5 : Entails.eval a c6448 := derived6448 a h
  have h6 : Entails.eval a c3684 := h 3683 (by decide)
  have h7 : Entails.eval a c4942 := h 4941 (by decide)
  have h8 : Entails.eval a c5491 := h 5490 (by decide)
  have h9 : Entails.eval a c4820 := h 4819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6450 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c5491, some c4942, some c4863, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6450 : lratChecker f6450 p6450 = .success := by decide +kernel
theorem unsat6450 : Unsatisfiable (PosFin 65) f6450 := by
  apply lratCheckerSound f6450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6450
  · intro a ha; simp [p6450] at ha; subst a; trivial
  · exact checked6450
theorem derived6450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6450 := by
  apply localUnsat_implies_entails f6450 [c6371, c6227, c5491, c4942, c4863] c6450 unsat6450 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5491 := h 5490 (by decide)
  have h3 : Entails.eval a c4942 := h 4941 (by decide)
  have h4 : Entails.eval a c4863 := h 4862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6451 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨61, by decide⟩, true), (⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3664, some c3915, some c5323, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p6451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6451 : lratChecker f6451 p6451 = .success := by decide +kernel
theorem unsat6451 : Unsatisfiable (PosFin 65) f6451 := by
  apply lratCheckerSound f6451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6451
  · intro a ha; simp [p6451] at ha; subst a; trivial
  · exact checked6451
theorem derived6451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6451 := by
  apply localUnsat_implies_entails f6451 [c3664, c3915, c5323] c6451 unsat6451 (by rfl) a
  have h0 : Entails.eval a c3664 := h 3663 (by decide)
  have h1 : Entails.eval a c3915 := h 3914 (by decide)
  have h2 : Entails.eval a c5323 := h 5322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6452 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6449, some c6451, some c6227, some c5034, some c6450, some c6439, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6452 : lratChecker f6452 p6452 = .success := by decide +kernel
theorem unsat6452 : Unsatisfiable (PosFin 65) f6452 := by
  apply lratCheckerSound f6452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6452
  · intro a ha; simp [p6452] at ha; subst a; trivial
  · exact checked6452
theorem derived6452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6452 := by
  apply localUnsat_implies_entails f6452 [c6371, c6449, c6451, c6227, c5034, c6450, c6439] c6452 unsat6452 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6449 := derived6449 a h
  have h2 : Entails.eval a c6451 := derived6451 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c5034 := h 5033 (by decide)
  have h5 : Entails.eval a c6450 := derived6450 a h
  have h6 : Entails.eval a c6439 := derived6439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6453 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨38, by decide⟩, true), (⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c5900, some c6173, some c3649, some c4884, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6453 : lratChecker f6453 p6453 = .success := by decide +kernel
theorem unsat6453 : Unsatisfiable (PosFin 65) f6453 := by
  apply lratCheckerSound f6453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6453
  · intro a ha; simp [p6453] at ha; subst a; trivial
  · exact checked6453
theorem derived6453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6453 := by
  apply localUnsat_implies_entails f6453 [c6371, c5900, c6173, c3649, c4884] c6453 unsat6453 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c5900 := derived5900 a h
  have h2 : Entails.eval a c6173 := derived6173 a h
  have h3 : Entails.eval a c3649 := h 3648 (by decide)
  have h4 : Entails.eval a c4884 := h 4883 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6454 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨38, by decide⟩, true), (⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3639, some c4879, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6454 : lratChecker f6454 p6454 = .success := by decide +kernel
theorem unsat6454 : Unsatisfiable (PosFin 65) f6454 := by
  apply lratCheckerSound f6454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6454
  · intro a ha; simp [p6454] at ha; subst a; trivial
  · exact checked6454
theorem derived6454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6454 := by
  apply localUnsat_implies_entails f6454 [c3639, c4879] c6454 unsat6454 (by rfl) a
  have h0 : Entails.eval a c3639 := h 3638 (by decide)
  have h1 : Entails.eval a c4879 := h 4878 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6455 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6449, some c6371, some c6227, some c6451, some c6452, some c6284, some c4762, some c5323, some c4920, some c6439, some c6454, some c6453, some c5714, some c5408, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6455 : lratChecker f6455 p6455 = .success := by decide +kernel
theorem unsat6455 : Unsatisfiable (PosFin 65) f6455 := by
  apply lratCheckerSound f6455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6455
  · intro a ha; simp [p6455] at ha; subst a; trivial
  · exact checked6455
theorem derived6455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6455 := by
  apply localUnsat_implies_entails f6455 [c6440, c6449, c6371, c6227, c6451, c6452, c6284, c4762, c5323, c4920, c6439, c6454, c6453, c5714, c5408] c6455 unsat6455 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6449 := derived6449 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6451 := derived6451 a h
  have h5 : Entails.eval a c6452 := derived6452 a h
  have h6 : Entails.eval a c6284 := derived6284 a h
  have h7 : Entails.eval a c4762 := h 4761 (by decide)
  have h8 : Entails.eval a c5323 := h 5322 (by decide)
  have h9 : Entails.eval a c4920 := h 4919 (by decide)
  have h10 : Entails.eval a c6439 := derived6439 a h
  have h11 : Entails.eval a c6454 := derived6454 a h
  have h12 : Entails.eval a c6453 := derived6453 a h
  have h13 : Entails.eval a c5714 := h 5713 (by decide)
  have h14 : Entails.eval a c5408 := h 5407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6456 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨46, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5714, some c5408, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6456 : lratChecker f6456 p6456 = .success := by decide +kernel
theorem unsat6456 : Unsatisfiable (PosFin 65) f6456 := by
  apply lratCheckerSound f6456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6456
  · intro a ha; simp [p6456] at ha; subst a; trivial
  · exact checked6456
theorem derived6456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6456 := by
  apply localUnsat_implies_entails f6456 [c5714, c5408] c6456 unsat6456 (by rfl) a
  have h0 : Entails.eval a c5714 := h 5713 (by decide)
  have h1 : Entails.eval a c5408 := h 5407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6457 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨38, by decide⟩, true), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6440, some c6449, some c6456, some c6454, some c6453, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6457 : lratChecker f6457 p6457 = .success := by decide +kernel
theorem unsat6457 : Unsatisfiable (PosFin 65) f6457 := by
  apply lratCheckerSound f6457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6457
  · intro a ha; simp [p6457] at ha; subst a; trivial
  · exact checked6457
theorem derived6457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6457 := by
  apply localUnsat_implies_entails f6457 [c6227, c6440, c6449, c6456, c6454, c6453] c6457 unsat6457 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6440 := derived6440 a h
  have h2 : Entails.eval a c6449 := derived6449 a h
  have h3 : Entails.eval a c6456 := derived6456 a h
  have h4 : Entails.eval a c6454 := derived6454 a h
  have h5 : Entails.eval a c6453 := derived6453 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6458 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4757, some c4764, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6458 : lratChecker f6458 p6458 = .success := by decide +kernel
theorem unsat6458 : Unsatisfiable (PosFin 65) f6458 := by
  apply lratCheckerSound f6458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6458
  · intro a ha; simp [p6458] at ha; subst a; trivial
  · exact checked6458
theorem derived6458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6458 := by
  apply localUnsat_implies_entails f6458 [c6227, c4757, c4764] c6458 unsat6458 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4757 := h 4756 (by decide)
  have h2 : Entails.eval a c4764 := h 4763 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6459 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨39, by decide⟩, true), (⟨61, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6287, some c3724, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6459 : lratChecker f6459 p6459 = .success := by decide +kernel
theorem unsat6459 : Unsatisfiable (PosFin 65) f6459 := by
  apply lratCheckerSound f6459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6459
  · intro a ha; simp [p6459] at ha; subst a; trivial
  · exact checked6459
theorem derived6459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6459 := by
  apply localUnsat_implies_entails f6459 [c6287, c3724] c6459 unsat6459 (by rfl) a
  have h0 : Entails.eval a c6287 := derived6287 a h
  have h1 : Entails.eval a c3724 := h 3723 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6460 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨61, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5334, some c5321, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6460 : lratChecker f6460 p6460 = .success := by decide +kernel
theorem unsat6460 : Unsatisfiable (PosFin 65) f6460 := by
  apply lratCheckerSound f6460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6460
  · intro a ha; simp [p6460] at ha; subst a; trivial
  · exact checked6460
theorem derived6460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6460 := by
  apply localUnsat_implies_entails f6460 [c6227, c5334, c5321] c6460 unsat6460 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5334 := h 5333 (by decide)
  have h2 : Entails.eval a c5321 := h 5320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6461 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6455, some c6440, some c6449, some c6227, some c6458, some c6459, some c6460, some c6456, some c6454, some c4925, some c3670, some c6439, some c6457, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6461 : lratChecker f6461 p6461 = .success := by decide +kernel
theorem unsat6461 : Unsatisfiable (PosFin 65) f6461 := by
  apply lratCheckerSound f6461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6461
  · intro a ha; simp [p6461] at ha; subst a; trivial
  · exact checked6461
theorem derived6461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6461 := by
  apply localUnsat_implies_entails f6461 [c6455, c6440, c6449, c6227, c6458, c6459, c6460, c6456, c6454, c4925, c3670, c6439, c6457] c6461 unsat6461 (by rfl) a
  have h0 : Entails.eval a c6455 := derived6455 a h
  have h1 : Entails.eval a c6440 := derived6440 a h
  have h2 : Entails.eval a c6449 := derived6449 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6458 := derived6458 a h
  have h5 : Entails.eval a c6459 := derived6459 a h
  have h6 : Entails.eval a c6460 := derived6460 a h
  have h7 : Entails.eval a c6456 := derived6456 a h
  have h8 : Entails.eval a c6454 := derived6454 a h
  have h9 : Entails.eval a c4925 := h 4924 (by decide)
  have h10 : Entails.eval a c3670 := h 3669 (by decide)
  have h11 : Entails.eval a c6439 := derived6439 a h
  have h12 : Entails.eval a c6457 := derived6457 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6462 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6461, some c6440, some c6449, some c6371, some c6227, some c5032, some c5900, some c5023, some c5082, some c4976, some c5395, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6462 : lratChecker f6462 p6462 = .success := by decide +kernel
theorem unsat6462 : Unsatisfiable (PosFin 65) f6462 := by
  apply lratCheckerSound f6462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6462
  · intro a ha; simp [p6462] at ha; subst a; trivial
  · exact checked6462
theorem derived6462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6462 := by
  apply localUnsat_implies_entails f6462 [c6461, c6440, c6449, c6371, c6227, c5032, c5900, c5023, c5082, c4976, c5395] c6462 unsat6462 (by rfl) a
  have h0 : Entails.eval a c6461 := derived6461 a h
  have h1 : Entails.eval a c6440 := derived6440 a h
  have h2 : Entails.eval a c6449 := derived6449 a h
  have h3 : Entails.eval a c6371 := derived6371 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c5032 := h 5031 (by decide)
  have h6 : Entails.eval a c5900 := derived5900 a h
  have h7 : Entails.eval a c5023 := h 5022 (by decide)
  have h8 : Entails.eval a c5082 := h 5081 (by decide)
  have h9 : Entails.eval a c4976 := h 4975 (by decide)
  have h10 : Entails.eval a c5395 := h 5394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6463 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5578, some c5590, some c5575, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p6463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6463 : lratChecker f6463 p6463 = .success := by decide +kernel
theorem unsat6463 : Unsatisfiable (PosFin 65) f6463 := by
  apply lratCheckerSound f6463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6463
  · intro a ha; simp [p6463] at ha; subst a; trivial
  · exact checked6463
theorem derived6463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6463 := by
  apply localUnsat_implies_entails f6463 [c5578, c5590, c5575] c6463 unsat6463 (by rfl) a
  have h0 : Entails.eval a c5578 := h 5577 (by decide)
  have h1 : Entails.eval a c5590 := h 5589 (by decide)
  have h2 : Entails.eval a c5575 := h 5574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6464 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨36, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4075, some c5408, some c3976, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6464 : lratChecker f6464 p6464 = .success := by decide +kernel
theorem unsat6464 : Unsatisfiable (PosFin 65) f6464 := by
  apply lratCheckerSound f6464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6464
  · intro a ha; simp [p6464] at ha; subst a; trivial
  · exact checked6464
theorem derived6464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6464 := by
  apply localUnsat_implies_entails f6464 [c4075, c5408, c3976] c6464 unsat6464 (by rfl) a
  have h0 : Entails.eval a c4075 := h 4074 (by decide)
  have h1 : Entails.eval a c5408 := h 5407 (by decide)
  have h2 : Entails.eval a c3976 := h 3975 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6465 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6461, some c6455, some c6440, some c6449, some c6227, some c6462, some c6439, some c6463, some c5490, some c3584, some c4651, some c6464, some c5324, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6465 : lratChecker f6465 p6465 = .success := by decide +kernel
theorem unsat6465 : Unsatisfiable (PosFin 65) f6465 := by
  apply lratCheckerSound f6465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6465
  · intro a ha; simp [p6465] at ha; subst a; trivial
  · exact checked6465
theorem derived6465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6465 := by
  apply localUnsat_implies_entails f6465 [c6461, c6455, c6440, c6449, c6227, c6462, c6439, c6463, c5490, c3584, c4651, c6464, c5324] c6465 unsat6465 (by rfl) a
  have h0 : Entails.eval a c6461 := derived6461 a h
  have h1 : Entails.eval a c6455 := derived6455 a h
  have h2 : Entails.eval a c6440 := derived6440 a h
  have h3 : Entails.eval a c6449 := derived6449 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6462 := derived6462 a h
  have h6 : Entails.eval a c6439 := derived6439 a h
  have h7 : Entails.eval a c6463 := derived6463 a h
  have h8 : Entails.eval a c5490 := h 5489 (by decide)
  have h9 : Entails.eval a c3584 := h 3583 (by decide)
  have h10 : Entails.eval a c4651 := h 4650 (by decide)
  have h11 : Entails.eval a c6464 := derived6464 a h
  have h12 : Entails.eval a c5324 := h 5323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6466 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨39, by decide⟩, false), (⟨61, by decide⟩, false), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5293, some c4143, some c4085, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6466 : lratChecker f6466 p6466 = .success := by decide +kernel
theorem unsat6466 : Unsatisfiable (PosFin 65) f6466 := by
  apply lratCheckerSound f6466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6466
  · intro a ha; simp [p6466] at ha; subst a; trivial
  · exact checked6466
theorem derived6466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6466 := by
  apply localUnsat_implies_entails f6466 [c5293, c4143, c4085] c6466 unsat6466 (by rfl) a
  have h0 : Entails.eval a c5293 := h 5292 (by decide)
  have h1 : Entails.eval a c4143 := h 4142 (by decide)
  have h2 : Entails.eval a c4085 := h 4084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6467 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨61, by decide⟩, false), (⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6434, some c3666, some c3670, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6467 : lratChecker f6467 p6467 = .success := by decide +kernel
theorem unsat6467 : Unsatisfiable (PosFin 65) f6467 := by
  apply lratCheckerSound f6467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6467
  · intro a ha; simp [p6467] at ha; subst a; trivial
  · exact checked6467
theorem derived6467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6467 := by
  apply localUnsat_implies_entails f6467 [c6434, c3666, c3670] c6467 unsat6467 (by rfl) a
  have h0 : Entails.eval a c6434 := derived6434 a h
  have h1 : Entails.eval a c3666 := h 3665 (by decide)
  have h2 : Entails.eval a c3670 := h 3669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6468 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6371, some c6227, some c6449, some c6455, some c6461, some c6465, some c6434, some c6466, some c6439, some c6467, some c4984, some c4983, some c4989, some c5950, some c4977, some c4976, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6468 : lratChecker f6468 p6468 = .success := by decide +kernel
theorem unsat6468 : Unsatisfiable (PosFin 65) f6468 := by
  apply lratCheckerSound f6468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6468
  · intro a ha; simp [p6468] at ha; subst a; trivial
  · exact checked6468
theorem derived6468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6468 := by
  apply localUnsat_implies_entails f6468 [c6440, c6371, c6227, c6449, c6455, c6461, c6465, c6434, c6466, c6439, c6467, c4984, c4983, c4989, c5950, c4977, c4976] c6468 unsat6468 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6449 := derived6449 a h
  have h4 : Entails.eval a c6455 := derived6455 a h
  have h5 : Entails.eval a c6461 := derived6461 a h
  have h6 : Entails.eval a c6465 := derived6465 a h
  have h7 : Entails.eval a c6434 := derived6434 a h
  have h8 : Entails.eval a c6466 := derived6466 a h
  have h9 : Entails.eval a c6439 := derived6439 a h
  have h10 : Entails.eval a c6467 := derived6467 a h
  have h11 : Entails.eval a c4984 := h 4983 (by decide)
  have h12 : Entails.eval a c4983 := h 4982 (by decide)
  have h13 : Entails.eval a c4989 := h 4988 (by decide)
  have h14 : Entails.eval a c5950 := derived5950 a h
  have h15 : Entails.eval a c4977 := h 4976 (by decide)
  have h16 : Entails.eval a c4976 := h 4975 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6469 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6371, some c6466, some c5273, some c4954, some c4972, some c5664, some c5797, some c5082, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6469 : lratChecker f6469 p6469 = .success := by decide +kernel
theorem unsat6469 : Unsatisfiable (PosFin 65) f6469 := by
  apply lratCheckerSound f6469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6469
  · intro a ha; simp [p6469] at ha; subst a; trivial
  · exact checked6469
theorem derived6469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6469 := by
  apply localUnsat_implies_entails f6469 [c6440, c6371, c6466, c5273, c4954, c4972, c5664, c5797, c5082] c6469 unsat6469 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6466 := derived6466 a h
  have h3 : Entails.eval a c5273 := h 5272 (by decide)
  have h4 : Entails.eval a c4954 := h 4953 (by decide)
  have h5 : Entails.eval a c4972 := h 4971 (by decide)
  have h6 : Entails.eval a c5664 := h 5663 (by decide)
  have h7 : Entails.eval a c5797 := h 5796 (by decide)
  have h8 : Entails.eval a c5082 := h 5081 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6470 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨33, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6458, some c5544, some c3435, some c5388, some c4244, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6470 : lratChecker f6470 p6470 = .success := by decide +kernel
theorem unsat6470 : Unsatisfiable (PosFin 65) f6470 := by
  apply lratCheckerSound f6470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6470
  · intro a ha; simp [p6470] at ha; subst a; trivial
  · exact checked6470
theorem derived6470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6470 := by
  apply localUnsat_implies_entails f6470 [c6458, c5544, c3435, c5388, c4244] c6470 unsat6470 (by rfl) a
  have h0 : Entails.eval a c6458 := derived6458 a h
  have h1 : Entails.eval a c5544 := h 5543 (by decide)
  have h2 : Entails.eval a c3435 := h 3434 (by decide)
  have h3 : Entails.eval a c5388 := h 5387 (by decide)
  have h4 : Entails.eval a c4244 := h 4243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6471 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6468, some c6440, some c6371, some c6470, some c6466, some c5273, some c6469, some c5164, some c4244, some c4868, some c5160, some c5159, some c3437, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6471 : lratChecker f6471 p6471 = .success := by decide +kernel
theorem unsat6471 : Unsatisfiable (PosFin 65) f6471 := by
  apply lratCheckerSound f6471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6471
  · intro a ha; simp [p6471] at ha; subst a; trivial
  · exact checked6471
theorem derived6471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6471 := by
  apply localUnsat_implies_entails f6471 [c6468, c6440, c6371, c6470, c6466, c5273, c6469, c5164, c4244, c4868, c5160, c5159, c3437] c6471 unsat6471 (by rfl) a
  have h0 : Entails.eval a c6468 := derived6468 a h
  have h1 : Entails.eval a c6440 := derived6440 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6470 := derived6470 a h
  have h4 : Entails.eval a c6466 := derived6466 a h
  have h5 : Entails.eval a c5273 := h 5272 (by decide)
  have h6 : Entails.eval a c6469 := derived6469 a h
  have h7 : Entails.eval a c5164 := h 5163 (by decide)
  have h8 : Entails.eval a c4244 := h 4243 (by decide)
  have h9 : Entails.eval a c4868 := h 4867 (by decide)
  have h10 : Entails.eval a c5160 := h 5159 (by decide)
  have h11 : Entails.eval a c5159 := h 5158 (by decide)
  have h12 : Entails.eval a c3437 := h 3436 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6472 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨37, by decide⟩, true), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6471, some c6468, some c6440, some c6371, some c6227, some c6466, some c5273, some c5164, some c4862, some c4244, some c5163, some c3437, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6472 : lratChecker f6472 p6472 = .success := by decide +kernel
theorem unsat6472 : Unsatisfiable (PosFin 65) f6472 := by
  apply lratCheckerSound f6472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6472
  · intro a ha; simp [p6472] at ha; subst a; trivial
  · exact checked6472
theorem derived6472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6472 := by
  apply localUnsat_implies_entails f6472 [c6471, c6468, c6440, c6371, c6227, c6466, c5273, c5164, c4862, c4244, c5163, c3437] c6472 unsat6472 (by rfl) a
  have h0 : Entails.eval a c6471 := derived6471 a h
  have h1 : Entails.eval a c6468 := derived6468 a h
  have h2 : Entails.eval a c6440 := derived6440 a h
  have h3 : Entails.eval a c6371 := derived6371 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6466 := derived6466 a h
  have h6 : Entails.eval a c5273 := h 5272 (by decide)
  have h7 : Entails.eval a c5164 := h 5163 (by decide)
  have h8 : Entails.eval a c4862 := h 4861 (by decide)
  have h9 : Entails.eval a c4244 := h 4243 (by decide)
  have h10 : Entails.eval a c5163 := h 5162 (by decide)
  have h11 : Entails.eval a c3437 := h 3436 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6473 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨57, by decide⟩, true), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6458, some c5544, some c5513, some c4881, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6473 : lratChecker f6473 p6473 = .success := by decide +kernel
theorem unsat6473 : Unsatisfiable (PosFin 65) f6473 := by
  apply lratCheckerSound f6473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6473
  · intro a ha; simp [p6473] at ha; subst a; trivial
  · exact checked6473
theorem derived6473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6473 := by
  apply localUnsat_implies_entails f6473 [c6227, c6458, c5544, c5513, c4881] c6473 unsat6473 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6458 := derived6458 a h
  have h2 : Entails.eval a c5544 := h 5543 (by decide)
  have h3 : Entails.eval a c5513 := h 5512 (by decide)
  have h4 : Entails.eval a c4881 := h 4880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6474 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6227, some c6471, some c6473, some c4960, some c6472, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6474 : lratChecker f6474 p6474 = .success := by decide +kernel
theorem unsat6474 : Unsatisfiable (PosFin 65) f6474 := by
  apply lratCheckerSound f6474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6474
  · intro a ha; simp [p6474] at ha; subst a; trivial
  · exact checked6474
theorem derived6474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6474 := by
  apply localUnsat_implies_entails f6474 [c6440, c6227, c6471, c6473, c4960, c6472] c6474 unsat6474 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6471 := derived6471 a h
  have h3 : Entails.eval a c6473 := derived6473 a h
  have h4 : Entails.eval a c4960 := h 4959 (by decide)
  have h5 : Entails.eval a c6472 := derived6472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6475 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨53, by decide⟩, true), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6458, some c5512, some c5536, some c4879, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6475 : lratChecker f6475 p6475 = .success := by decide +kernel
theorem unsat6475 : Unsatisfiable (PosFin 65) f6475 := by
  apply lratCheckerSound f6475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6475
  · intro a ha; simp [p6475] at ha; subst a; trivial
  · exact checked6475
theorem derived6475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6475 := by
  apply localUnsat_implies_entails f6475 [c6227, c6458, c5512, c5536, c4879] c6475 unsat6475 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6458 := derived6458 a h
  have h2 : Entails.eval a c5512 := h 5511 (by decide)
  have h3 : Entails.eval a c5536 := h 5535 (by decide)
  have h4 : Entails.eval a c4879 := h 4878 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6476 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6468, some c6440, some c6227, some c6474, some c6475, some c5265, some c4234, some c4860, some c3426, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6476 : lratChecker f6476 p6476 = .success := by decide +kernel
theorem unsat6476 : Unsatisfiable (PosFin 65) f6476 := by
  apply lratCheckerSound f6476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6476
  · intro a ha; simp [p6476] at ha; subst a; trivial
  · exact checked6476
theorem derived6476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6476 := by
  apply localUnsat_implies_entails f6476 [c6468, c6440, c6227, c6474, c6475, c5265, c4234, c4860, c3426] c6476 unsat6476 (by rfl) a
  have h0 : Entails.eval a c6468 := derived6468 a h
  have h1 : Entails.eval a c6440 := derived6440 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6474 := derived6474 a h
  have h4 : Entails.eval a c6475 := derived6475 a h
  have h5 : Entails.eval a c5265 := h 5264 (by decide)
  have h6 : Entails.eval a c4234 := h 4233 (by decide)
  have h7 : Entails.eval a c4860 := h 4859 (by decide)
  have h8 : Entails.eval a c3426 := h 3425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6477 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4072, some c4713, some c3426, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6477 : lratChecker f6477 p6477 = .success := by decide +kernel
theorem unsat6477 : Unsatisfiable (PosFin 65) f6477 := by
  apply lratCheckerSound f6477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6477
  · intro a ha; simp [p6477] at ha; subst a; trivial
  · exact checked6477
theorem derived6477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6477 := by
  apply localUnsat_implies_entails f6477 [c4072, c4713, c3426] c6477 unsat6477 (by rfl) a
  have h0 : Entails.eval a c4072 := h 4071 (by decide)
  have h1 : Entails.eval a c4713 := h 4712 (by decide)
  have h2 : Entails.eval a c3426 := h 3425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6478 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6468, some c6440, some c6227, some c6476, some c6477, some c4085, some c4720, some c3435, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6478 : lratChecker f6478 p6478 = .success := by decide +kernel
theorem unsat6478 : Unsatisfiable (PosFin 65) f6478 := by
  apply lratCheckerSound f6478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6478
  · intro a ha; simp [p6478] at ha; subst a; trivial
  · exact checked6478
theorem derived6478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6478 := by
  apply localUnsat_implies_entails f6478 [c6468, c6440, c6227, c6476, c6477, c4085, c4720, c3435] c6478 unsat6478 (by rfl) a
  have h0 : Entails.eval a c6468 := derived6468 a h
  have h1 : Entails.eval a c6440 := derived6440 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6476 := derived6476 a h
  have h4 : Entails.eval a c6477 := derived6477 a h
  have h5 : Entails.eval a c4085 := h 4084 (by decide)
  have h6 : Entails.eval a c4720 := h 4719 (by decide)
  have h7 : Entails.eval a c3435 := h 3434 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6479 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4077, some c4717, some c3430, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6479 : lratChecker f6479 p6479 = .success := by decide +kernel
theorem unsat6479 : Unsatisfiable (PosFin 65) f6479 := by
  apply lratCheckerSound f6479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6479
  · intro a ha; simp [p6479] at ha; subst a; trivial
  · exact checked6479
theorem derived6479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6479 := by
  apply localUnsat_implies_entails f6479 [c4077, c4717, c3430] c6479 unsat6479 (by rfl) a
  have h0 : Entails.eval a c4077 := h 4076 (by decide)
  have h1 : Entails.eval a c4717 := h 4716 (by decide)
  have h2 : Entails.eval a c3430 := h 3429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6480 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨61, by decide⟩, true), (⟨33, by decide⟩, false), (⟨51, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c3481, some c3430, some c3458, some c4838, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6480 : lratChecker f6480 p6480 = .success := by decide +kernel
theorem unsat6480 : Unsatisfiable (PosFin 65) f6480 := by
  apply lratCheckerSound f6480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6480
  · intro a ha; simp [p6480] at ha; subst a; trivial
  · exact checked6480
theorem derived6480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6480 := by
  apply localUnsat_implies_entails f6480 [c6371, c6227, c3481, c3430, c3458, c4838] c6480 unsat6480 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c3481 := h 3480 (by decide)
  have h3 : Entails.eval a c3430 := h 3429 (by decide)
  have h4 : Entails.eval a c3458 := h 3457 (by decide)
  have h5 : Entails.eval a c4838 := h 4837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived6480

end CochromaticTwenty.Certificates.FixedCore1
