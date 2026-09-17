import MerLeanExperiment.Certificates.FixedCore1.Steps0300_0399

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6281 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3719, some c5514, some c4882, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6281 : lratChecker f6281 p6281 = .success := by decide +kernel
theorem unsat6281 : Unsatisfiable (PosFin 65) f6281 := by
  apply lratCheckerSound f6281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6281
  · intro a ha; simp [p6281] at ha; subst a; trivial
  · exact checked6281
theorem derived6281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6281 := by
  apply localUnsat_implies_entails f6281 [c3719, c5514, c4882] c6281 unsat6281 (by rfl) a
  have h0 : Entails.eval a c3719 := h 3718 (by decide)
  have h1 : Entails.eval a c5514 := h 5513 (by decide)
  have h2 : Entails.eval a c4882 := h 4881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6282 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3728, some c3724, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6282 : lratChecker f6282 p6282 = .success := by decide +kernel
theorem unsat6282 : Unsatisfiable (PosFin 65) f6282 := by
  apply lratCheckerSound f6282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6282
  · intro a ha; simp [p6282] at ha; subst a; trivial
  · exact checked6282
theorem derived6282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6282 := by
  apply localUnsat_implies_entails f6282 [c6227, c3728, c3724] c6282 unsat6282 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3728 := h 3727 (by decide)
  have h2 : Entails.eval a c3724 := h 3723 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6283 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4342, some c4924, some c4883, some c4634, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6283 : lratChecker f6283 p6283 = .success := by decide +kernel
theorem unsat6283 : Unsatisfiable (PosFin 65) f6283 := by
  apply lratCheckerSound f6283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6283
  · intro a ha; simp [p6283] at ha; subst a; trivial
  · exact checked6283
theorem derived6283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6283 := by
  apply localUnsat_implies_entails f6283 [c4342, c4924, c4883, c4634] c6283 unsat6283 (by rfl) a
  have h0 : Entails.eval a c4342 := h 4341 (by decide)
  have h1 : Entails.eval a c4924 := h 4923 (by decide)
  have h2 : Entails.eval a c4883 := h 4882 (by decide)
  have h3 : Entails.eval a c4634 := h 4633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6284 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨61, by decide⟩, true), (⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5531, some c5538, some c5527, some c5549, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6284 : lratChecker f6284 p6284 = .success := by decide +kernel
theorem unsat6284 : Unsatisfiable (PosFin 65) f6284 := by
  apply lratCheckerSound f6284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6284
  · intro a ha; simp [p6284] at ha; subst a; trivial
  · exact checked6284
theorem derived6284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6284 := by
  apply localUnsat_implies_entails f6284 [c5531, c5538, c5527, c5549] c6284 unsat6284 (by rfl) a
  have h0 : Entails.eval a c5531 := h 5530 (by decide)
  have h1 : Entails.eval a c5538 := h 5537 (by decide)
  have h2 : Entails.eval a c5527 := h 5526 (by decide)
  have h3 : Entails.eval a c5549 := h 5548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6285 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨46, by decide⟩, false), (⟨53, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3710, some c4885, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6285 : lratChecker f6285 p6285 = .success := by decide +kernel
theorem unsat6285 : Unsatisfiable (PosFin 65) f6285 := by
  apply lratCheckerSound f6285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6285
  · intro a ha; simp [p6285] at ha; subst a; trivial
  · exact checked6285
theorem derived6285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6285 := by
  apply localUnsat_implies_entails f6285 [c3710, c4885] c6285 unsat6285 (by rfl) a
  have h0 : Entails.eval a c3710 := h 3709 (by decide)
  have h1 : Entails.eval a c4885 := h 4884 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6286 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6280, some c6227, some c6283, some c6285, some c6232, some c5335, some c3650, some c5720, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6286 : lratChecker f6286 p6286 = .success := by decide +kernel
theorem unsat6286 : Unsatisfiable (PosFin 65) f6286 := by
  apply lratCheckerSound f6286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6286
  · intro a ha; simp [p6286] at ha; subst a; trivial
  · exact checked6286
theorem derived6286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6286 := by
  apply localUnsat_implies_entails f6286 [c6280, c6227, c6283, c6285, c6232, c5335, c3650, c5720] c6286 unsat6286 (by rfl) a
  have h0 : Entails.eval a c6280 := derived6280 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6283 := derived6283 a h
  have h3 : Entails.eval a c6285 := derived6285 a h
  have h4 : Entails.eval a c6232 := derived6232 a h
  have h5 : Entails.eval a c5335 := h 5334 (by decide)
  have h6 : Entails.eval a c3650 := h 3649 (by decide)
  have h7 : Entails.eval a c5720 := h 5719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6287 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨46, by decide⟩, true), (⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3723, some c3717, some c3719, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6287 : lratChecker f6287 p6287 = .success := by decide +kernel
theorem unsat6287 : Unsatisfiable (PosFin 65) f6287 := by
  apply lratCheckerSound f6287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6287
  · intro a ha; simp [p6287] at ha; subst a; trivial
  · exact checked6287
theorem derived6287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6287 := by
  apply localUnsat_implies_entails f6287 [c6227, c3723, c3717, c3719] c6287 unsat6287 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3723 := h 3722 (by decide)
  have h2 : Entails.eval a c3717 := h 3716 (by decide)
  have h3 : Entails.eval a c3719 := h 3718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6288 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6286, some c6287, some c3724, some c6282, some c3720, some c3719, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6288 : lratChecker f6288 p6288 = .success := by decide +kernel
theorem unsat6288 : Unsatisfiable (PosFin 65) f6288 := by
  apply lratCheckerSound f6288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6288
  · intro a ha; simp [p6288] at ha; subst a; trivial
  · exact checked6288
theorem derived6288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6288 := by
  apply localUnsat_implies_entails f6288 [c6227, c6286, c6287, c3724, c6282, c3720, c3719] c6288 unsat6288 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6286 := derived6286 a h
  have h2 : Entails.eval a c6287 := derived6287 a h
  have h3 : Entails.eval a c3724 := h 3723 (by decide)
  have h4 : Entails.eval a c6282 := derived6282 a h
  have h5 : Entails.eval a c3720 := h 3719 (by decide)
  have h6 : Entails.eval a c3719 := h 3718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6289 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨59, by decide⟩, false), (⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨51, by decide⟩, false), (⟨58, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5480, some c5734, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p6289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6289 : lratChecker f6289 p6289 = .success := by decide +kernel
theorem unsat6289 : Unsatisfiable (PosFin 65) f6289 := by
  apply lratCheckerSound f6289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6289
  · intro a ha; simp [p6289] at ha; subst a; trivial
  · exact checked6289
theorem derived6289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6289 := by
  apply localUnsat_implies_entails f6289 [c5480, c5734] c6289 unsat6289 (by rfl) a
  have h0 : Entails.eval a c5480 := h 5479 (by decide)
  have h1 : Entails.eval a c5734 := h 5733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6290 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨42, by decide⟩, false), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨51, by decide⟩, false), (⟨58, by decide⟩, false), (⟨46, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6086, some c5883, some c6289, some c4357, some c5737, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6290 : lratChecker f6290 p6290 = .success := by decide +kernel
theorem unsat6290 : Unsatisfiable (PosFin 65) f6290 := by
  apply lratCheckerSound f6290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6290
  · intro a ha; simp [p6290] at ha; subst a; trivial
  · exact checked6290
theorem derived6290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6290 := by
  apply localUnsat_implies_entails f6290 [c6086, c5883, c6289, c4357, c5737] c6290 unsat6290 (by rfl) a
  have h0 : Entails.eval a c6086 := derived6086 a h
  have h1 : Entails.eval a c5883 := derived5883 a h
  have h2 : Entails.eval a c6289 := derived6289 a h
  have h3 : Entails.eval a c4357 := h 4356 (by decide)
  have h4 : Entails.eval a c5737 := h 5736 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6291 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨36, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4358, some c5737, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6291 : lratChecker f6291 p6291 = .success := by decide +kernel
theorem unsat6291 : Unsatisfiable (PosFin 65) f6291 := by
  apply lratCheckerSound f6291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6291
  · intro a ha; simp [p6291] at ha; subst a; trivial
  · exact checked6291
theorem derived6291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6291 := by
  apply localUnsat_implies_entails f6291 [c4358, c5737] c6291 unsat6291 (by rfl) a
  have h0 : Entails.eval a c4358 := h 4357 (by decide)
  have h1 : Entails.eval a c5737 := h 5736 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6292 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨61, by decide⟩, false), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3668, some c5589, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6292 : lratChecker f6292 p6292 = .success := by decide +kernel
theorem unsat6292 : Unsatisfiable (PosFin 65) f6292 := by
  apply lratCheckerSound f6292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6292
  · intro a ha; simp [p6292] at ha; subst a; trivial
  · exact checked6292
theorem derived6292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6292 := by
  apply localUnsat_implies_entails f6292 [c3668, c5589] c6292 unsat6292 (by rfl) a
  have h0 : Entails.eval a c3668 := h 3667 (by decide)
  have h1 : Entails.eval a c5589 := h 5588 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6293 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨58, by decide⟩, false), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3595, some c6288, some c6280, some c6227, some c5005, some c4961, some c3647, some c4420, some c3986, some c5102, some c4165, some c4087, some c3747, some c5830, some c5890, some c6290, some c6292, some c6291, some c5734, some c4892, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked6293 : lratChecker f6293 p6293 = .success := by decide +kernel
theorem unsat6293 : Unsatisfiable (PosFin 65) f6293 := by
  apply lratCheckerSound f6293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6293
  · intro a ha; simp [p6293] at ha; subst a; trivial
  · exact checked6293
theorem derived6293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6293 := by
  apply localUnsat_implies_entails f6293 [c3595, c6288, c6280, c6227, c5005, c4961, c3647, c4420, c3986, c5102, c4165, c4087, c3747, c5830, c5890, c6290, c6292, c6291, c5734, c4892] c6293 unsat6293 (by rfl) a
  have h0 : Entails.eval a c3595 := h 3594 (by decide)
  have h1 : Entails.eval a c6288 := derived6288 a h
  have h2 : Entails.eval a c6280 := derived6280 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c5005 := h 5004 (by decide)
  have h5 : Entails.eval a c4961 := h 4960 (by decide)
  have h6 : Entails.eval a c3647 := h 3646 (by decide)
  have h7 : Entails.eval a c4420 := h 4419 (by decide)
  have h8 : Entails.eval a c3986 := h 3985 (by decide)
  have h9 : Entails.eval a c5102 := h 5101 (by decide)
  have h10 : Entails.eval a c4165 := h 4164 (by decide)
  have h11 : Entails.eval a c4087 := h 4086 (by decide)
  have h12 : Entails.eval a c3747 := h 3746 (by decide)
  have h13 : Entails.eval a c5830 := h 5829 (by decide)
  have h14 : Entails.eval a c5890 := derived5890 a h
  have h15 : Entails.eval a c6290 := derived6290 a h
  have h16 : Entails.eval a c6292 := derived6292 a h
  have h17 : Entails.eval a c6291 := derived6291 a h
  have h18 : Entails.eval a c5734 := h 5733 (by decide)
  have h19 : Entails.eval a c4892 := h 4891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6294 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4946, some c5490, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6294 : lratChecker f6294 p6294 = .success := by decide +kernel
theorem unsat6294 : Unsatisfiable (PosFin 65) f6294 := by
  apply lratCheckerSound f6294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6294
  · intro a ha; simp [p6294] at ha; subst a; trivial
  · exact checked6294
theorem derived6294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6294 := by
  apply localUnsat_implies_entails f6294 [c4946, c5490] c6294 unsat6294 (by rfl) a
  have h0 : Entails.eval a c4946 := h 4945 (by decide)
  have h1 : Entails.eval a c5490 := h 5489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6295 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨58, by decide⟩, false), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6293, some c3595, some c6288, some c6280, some c6227, some c4002, some c4266, some c5074, some c4165, some c6294, some c3772, some c3921, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6295 : lratChecker f6295 p6295 = .success := by decide +kernel
theorem unsat6295 : Unsatisfiable (PosFin 65) f6295 := by
  apply lratCheckerSound f6295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6295
  · intro a ha; simp [p6295] at ha; subst a; trivial
  · exact checked6295
theorem derived6295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6295 := by
  apply localUnsat_implies_entails f6295 [c6293, c3595, c6288, c6280, c6227, c4002, c4266, c5074, c4165, c6294, c3772, c3921] c6295 unsat6295 (by rfl) a
  have h0 : Entails.eval a c6293 := derived6293 a h
  have h1 : Entails.eval a c3595 := h 3594 (by decide)
  have h2 : Entails.eval a c6288 := derived6288 a h
  have h3 : Entails.eval a c6280 := derived6280 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c4002 := h 4001 (by decide)
  have h6 : Entails.eval a c4266 := h 4265 (by decide)
  have h7 : Entails.eval a c5074 := h 5073 (by decide)
  have h8 : Entails.eval a c4165 := h 4164 (by decide)
  have h9 : Entails.eval a c6294 := derived6294 a h
  have h10 : Entails.eval a c3772 := h 3771 (by decide)
  have h11 : Entails.eval a c3921 := h 3920 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6296 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3595, some c6295, some c3904, some c3754, some c5102, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6296 : lratChecker f6296 p6296 = .success := by decide +kernel
theorem unsat6296 : Unsatisfiable (PosFin 65) f6296 := by
  apply lratCheckerSound f6296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6296
  · intro a ha; simp [p6296] at ha; subst a; trivial
  · exact checked6296
theorem derived6296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6296 := by
  apply localUnsat_implies_entails f6296 [c3595, c6295, c3904, c3754, c5102] c6296 unsat6296 (by rfl) a
  have h0 : Entails.eval a c3595 := h 3594 (by decide)
  have h1 : Entails.eval a c6295 := derived6295 a h
  have h2 : Entails.eval a c3904 := h 3903 (by decide)
  have h3 : Entails.eval a c3754 := h 3753 (by decide)
  have h4 : Entails.eval a c5102 := h 5101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6297 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6280, some c3897, some c3979, some c3747, some c4266, some c4483, some c3957, some c5699, some c4521, some c6296, some c6288, some c6227, some c4973, some c5014, some c6272, some c5063, some c4330, some c4907, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6297 : lratChecker f6297 p6297 = .success := by decide +kernel
theorem unsat6297 : Unsatisfiable (PosFin 65) f6297 := by
  apply lratCheckerSound f6297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6297
  · intro a ha; simp [p6297] at ha; subst a; trivial
  · exact checked6297
theorem derived6297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6297 := by
  apply localUnsat_implies_entails f6297 [c6280, c3897, c3979, c3747, c4266, c4483, c3957, c5699, c4521, c6296, c6288, c6227, c4973, c5014, c6272, c5063, c4330, c4907] c6297 unsat6297 (by rfl) a
  have h0 : Entails.eval a c6280 := derived6280 a h
  have h1 : Entails.eval a c3897 := h 3896 (by decide)
  have h2 : Entails.eval a c3979 := h 3978 (by decide)
  have h3 : Entails.eval a c3747 := h 3746 (by decide)
  have h4 : Entails.eval a c4266 := h 4265 (by decide)
  have h5 : Entails.eval a c4483 := h 4482 (by decide)
  have h6 : Entails.eval a c3957 := h 3956 (by decide)
  have h7 : Entails.eval a c5699 := h 5698 (by decide)
  have h8 : Entails.eval a c4521 := h 4520 (by decide)
  have h9 : Entails.eval a c6296 := derived6296 a h
  have h10 : Entails.eval a c6288 := derived6288 a h
  have h11 : Entails.eval a c6227 := derived6227 a h
  have h12 : Entails.eval a c4973 := h 4972 (by decide)
  have h13 : Entails.eval a c5014 := h 5013 (by decide)
  have h14 : Entails.eval a c6272 := derived6272 a h
  have h15 : Entails.eval a c5063 := h 5062 (by decide)
  have h16 : Entails.eval a c4330 := h 4329 (by decide)
  have h17 : Entails.eval a c4907 := h 4906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6298 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6296, some c6280, some c6227, some c3747, some c3897, some c5699, some c3979, some c6297, some c3598, some c3601, some c5221, some c4330, some c4906, some c3614, some c4907, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6298 : lratChecker f6298 p6298 = .success := by decide +kernel
theorem unsat6298 : Unsatisfiable (PosFin 65) f6298 := by
  apply lratCheckerSound f6298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6298
  · intro a ha; simp [p6298] at ha; subst a; trivial
  · exact checked6298
theorem derived6298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6298 := by
  apply localUnsat_implies_entails f6298 [c6296, c6280, c6227, c3747, c3897, c5699, c3979, c6297, c3598, c3601, c5221, c4330, c4906, c3614, c4907] c6298 unsat6298 (by rfl) a
  have h0 : Entails.eval a c6296 := derived6296 a h
  have h1 : Entails.eval a c6280 := derived6280 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c3747 := h 3746 (by decide)
  have h4 : Entails.eval a c3897 := h 3896 (by decide)
  have h5 : Entails.eval a c5699 := h 5698 (by decide)
  have h6 : Entails.eval a c3979 := h 3978 (by decide)
  have h7 : Entails.eval a c6297 := derived6297 a h
  have h8 : Entails.eval a c3598 := h 3597 (by decide)
  have h9 : Entails.eval a c3601 := h 3600 (by decide)
  have h10 : Entails.eval a c5221 := h 5220 (by decide)
  have h11 : Entails.eval a c4330 := h 4329 (by decide)
  have h12 : Entails.eval a c4906 := h 4905 (by decide)
  have h13 : Entails.eval a c3614 := h 3613 (by decide)
  have h14 : Entails.eval a c4907 := h 4906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6299 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨47, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨39, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4266, some c5825, some c4521, some c3957, some c5292, some c5293, some c5016, some c4065, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6299 : lratChecker f6299 p6299 = .success := by decide +kernel
theorem unsat6299 : Unsatisfiable (PosFin 65) f6299 := by
  apply lratCheckerSound f6299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6299
  · intro a ha; simp [p6299] at ha; subst a; trivial
  · exact checked6299
theorem derived6299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6299 := by
  apply localUnsat_implies_entails f6299 [c4266, c5825, c4521, c3957, c5292, c5293, c5016, c4065] c6299 unsat6299 (by rfl) a
  have h0 : Entails.eval a c4266 := h 4265 (by decide)
  have h1 : Entails.eval a c5825 := h 5824 (by decide)
  have h2 : Entails.eval a c4521 := h 4520 (by decide)
  have h3 : Entails.eval a c3957 := h 3956 (by decide)
  have h4 : Entails.eval a c5292 := h 5291 (by decide)
  have h5 : Entails.eval a c5293 := h 5292 (by decide)
  have h6 : Entails.eval a c5016 := h 5015 (by decide)
  have h7 : Entails.eval a c4065 := h 4064 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6300 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨34, by decide⟩, true), (⟨47, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3598, some c3601, some c5589, some c4330, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6300 : lratChecker f6300 p6300 = .success := by decide +kernel
theorem unsat6300 : Unsatisfiable (PosFin 65) f6300 := by
  apply lratCheckerSound f6300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6300
  · intro a ha; simp [p6300] at ha; subst a; trivial
  · exact checked6300
theorem derived6300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6300 := by
  apply localUnsat_implies_entails f6300 [c3598, c3601, c5589, c4330] c6300 unsat6300 (by rfl) a
  have h0 : Entails.eval a c3598 := h 3597 (by decide)
  have h1 : Entails.eval a c3601 := h 3600 (by decide)
  have h2 : Entails.eval a c5589 := h 5588 (by decide)
  have h3 : Entails.eval a c4330 := h 4329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6301 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨42, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5273, some c5474, some c6292, some c5356, some c4617, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6301 : lratChecker f6301 p6301 = .success := by decide +kernel
theorem unsat6301 : Unsatisfiable (PosFin 65) f6301 := by
  apply lratCheckerSound f6301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6301
  · intro a ha; simp [p6301] at ha; subst a; trivial
  · exact checked6301
theorem derived6301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6301 := by
  apply localUnsat_implies_entails f6301 [c6227, c5273, c5474, c6292, c5356, c4617] c6301 unsat6301 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5273 := h 5272 (by decide)
  have h2 : Entails.eval a c5474 := h 5473 (by decide)
  have h3 : Entails.eval a c6292 := derived6292 a h
  have h4 : Entails.eval a c5356 := h 5355 (by decide)
  have h5 : Entails.eval a c4617 := h 4616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6302 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨58, by decide⟩, true), (⟨39, by decide⟩, false), (⟨63, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4973, some c5017, some c5047, some c5358, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6302 : lratChecker f6302 p6302 = .success := by decide +kernel
theorem unsat6302 : Unsatisfiable (PosFin 65) f6302 := by
  apply lratCheckerSound f6302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6302
  · intro a ha; simp [p6302] at ha; subst a; trivial
  · exact checked6302
theorem derived6302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6302 := by
  apply localUnsat_implies_entails f6302 [c4973, c5017, c5047, c5358] c6302 unsat6302 (by rfl) a
  have h0 : Entails.eval a c4973 := h 4972 (by decide)
  have h1 : Entails.eval a c5017 := h 5016 (by decide)
  have h2 : Entails.eval a c5047 := h 5046 (by decide)
  have h3 : Entails.eval a c5358 := h 5357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6303 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6288, some c6280, some c6227, some c6296, some c6298, some c4002, some c4266, some c6299, some c4483, some c4165, some c6300, some c6301, some c6302, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6303 : lratChecker f6303 p6303 = .success := by decide +kernel
theorem unsat6303 : Unsatisfiable (PosFin 65) f6303 := by
  apply lratCheckerSound f6303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6303
  · intro a ha; simp [p6303] at ha; subst a; trivial
  · exact checked6303
theorem derived6303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6303 := by
  apply localUnsat_implies_entails f6303 [c6288, c6280, c6227, c6296, c6298, c4002, c4266, c6299, c4483, c4165, c6300, c6301, c6302] c6303 unsat6303 (by rfl) a
  have h0 : Entails.eval a c6288 := derived6288 a h
  have h1 : Entails.eval a c6280 := derived6280 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6296 := derived6296 a h
  have h4 : Entails.eval a c6298 := derived6298 a h
  have h5 : Entails.eval a c4002 := h 4001 (by decide)
  have h6 : Entails.eval a c4266 := h 4265 (by decide)
  have h7 : Entails.eval a c6299 := derived6299 a h
  have h8 : Entails.eval a c4483 := h 4482 (by decide)
  have h9 : Entails.eval a c4165 := h 4164 (by decide)
  have h10 : Entails.eval a c6300 := derived6300 a h
  have h11 : Entails.eval a c6301 := derived6301 a h
  have h12 : Entails.eval a c6302 := derived6302 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6304 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨58, by decide⟩, true), (⟨46, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6302, some c3601, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6304 : lratChecker f6304 p6304 = .success := by decide +kernel
theorem unsat6304 : Unsatisfiable (PosFin 65) f6304 := by
  apply lratCheckerSound f6304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6304
  · intro a ha; simp [p6304] at ha; subst a; trivial
  · exact checked6304
theorem derived6304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6304 := by
  apply localUnsat_implies_entails f6304 [c6302, c3601] c6304 unsat6304 (by rfl) a
  have h0 : Entails.eval a c6302 := derived6302 a h
  have h1 : Entails.eval a c3601 := h 3600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6305 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨48, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5585, some c4628, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p6305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6305 : lratChecker f6305 p6305 = .success := by decide +kernel
theorem unsat6305 : Unsatisfiable (PosFin 65) f6305 := by
  apply lratCheckerSound f6305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6305
  · intro a ha; simp [p6305] at ha; subst a; trivial
  · exact checked6305
theorem derived6305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6305 := by
  apply localUnsat_implies_entails f6305 [c5585, c4628] c6305 unsat6305 (by rfl) a
  have h0 : Entails.eval a c5585 := h 5584 (by decide)
  have h1 : Entails.eval a c4628 := h 4627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6306 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨46, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3924, some c4368, some c4908, some c4434, some c6304, some c6305, some c4966, some c3590, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6306 : lratChecker f6306 p6306 = .success := by decide +kernel
theorem unsat6306 : Unsatisfiable (PosFin 65) f6306 := by
  apply lratCheckerSound f6306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6306
  · intro a ha; simp [p6306] at ha; subst a; trivial
  · exact checked6306
theorem derived6306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6306 := by
  apply localUnsat_implies_entails f6306 [c6227, c3924, c4368, c4908, c4434, c6304, c6305, c4966, c3590] c6306 unsat6306 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3924 := h 3923 (by decide)
  have h2 : Entails.eval a c4368 := h 4367 (by decide)
  have h3 : Entails.eval a c4908 := h 4907 (by decide)
  have h4 : Entails.eval a c4434 := h 4433 (by decide)
  have h5 : Entails.eval a c6304 := derived6304 a h
  have h6 : Entails.eval a c6305 := derived6305 a h
  have h7 : Entails.eval a c4966 := h 4965 (by decide)
  have h8 : Entails.eval a c3590 := h 3589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6307 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨48, by decide⟩, false), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6280, some c6288, some c6303, some c6306, some c3650, some c3904, some c5288, some c5575, some c4940, some c4939, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6307 : lratChecker f6307 p6307 = .success := by decide +kernel
theorem unsat6307 : Unsatisfiable (PosFin 65) f6307 := by
  apply lratCheckerSound f6307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6307
  · intro a ha; simp [p6307] at ha; subst a; trivial
  · exact checked6307
theorem derived6307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6307 := by
  apply localUnsat_implies_entails f6307 [c6280, c6288, c6303, c6306, c3650, c3904, c5288, c5575, c4940, c4939] c6307 unsat6307 (by rfl) a
  have h0 : Entails.eval a c6280 := derived6280 a h
  have h1 : Entails.eval a c6288 := derived6288 a h
  have h2 : Entails.eval a c6303 := derived6303 a h
  have h3 : Entails.eval a c6306 := derived6306 a h
  have h4 : Entails.eval a c3650 := h 3649 (by decide)
  have h5 : Entails.eval a c3904 := h 3903 (by decide)
  have h6 : Entails.eval a c5288 := h 5287 (by decide)
  have h7 : Entails.eval a c5575 := h 5574 (by decide)
  have h8 : Entails.eval a c4940 := h 4939 (by decide)
  have h9 : Entails.eval a c4939 := h 4938 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6308 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6280, some c6288, some c6303, some c6306, some c3595, some c6227, some c6307, some c4902, some c4895, some c5230, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6308 : lratChecker f6308 p6308 = .success := by decide +kernel
theorem unsat6308 : Unsatisfiable (PosFin 65) f6308 := by
  apply lratCheckerSound f6308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6308
  · intro a ha; simp [p6308] at ha; subst a; trivial
  · exact checked6308
theorem derived6308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6308 := by
  apply localUnsat_implies_entails f6308 [c6280, c6288, c6303, c6306, c3595, c6227, c6307, c4902, c4895, c5230] c6308 unsat6308 (by rfl) a
  have h0 : Entails.eval a c6280 := derived6280 a h
  have h1 : Entails.eval a c6288 := derived6288 a h
  have h2 : Entails.eval a c6303 := derived6303 a h
  have h3 : Entails.eval a c6306 := derived6306 a h
  have h4 : Entails.eval a c3595 := h 3594 (by decide)
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c6307 := derived6307 a h
  have h7 : Entails.eval a c4902 := h 4901 (by decide)
  have h8 : Entails.eval a c4895 := h 4894 (by decide)
  have h9 : Entails.eval a c5230 := h 5229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6309 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6280, some c6288, some c6303, some c6306, some c3595, some c6227, some c3912, some c3927, some c3925, some c5005, some c4961, some c3918, some c5341, some c5340, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6309 : lratChecker f6309 p6309 = .success := by decide +kernel
theorem unsat6309 : Unsatisfiable (PosFin 65) f6309 := by
  apply lratCheckerSound f6309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6309
  · intro a ha; simp [p6309] at ha; subst a; trivial
  · exact checked6309
theorem derived6309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6309 := by
  apply localUnsat_implies_entails f6309 [c6280, c6288, c6303, c6306, c3595, c6227, c3912, c3927, c3925, c5005, c4961, c3918, c5341, c5340] c6309 unsat6309 (by rfl) a
  have h0 : Entails.eval a c6280 := derived6280 a h
  have h1 : Entails.eval a c6288 := derived6288 a h
  have h2 : Entails.eval a c6303 := derived6303 a h
  have h3 : Entails.eval a c6306 := derived6306 a h
  have h4 : Entails.eval a c3595 := h 3594 (by decide)
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c3912 := h 3911 (by decide)
  have h7 : Entails.eval a c3927 := h 3926 (by decide)
  have h8 : Entails.eval a c3925 := h 3924 (by decide)
  have h9 : Entails.eval a c5005 := h 5004 (by decide)
  have h10 : Entails.eval a c4961 := h 4960 (by decide)
  have h11 : Entails.eval a c3918 := h 3917 (by decide)
  have h12 : Entails.eval a c5341 := h 5340 (by decide)
  have h13 : Entails.eval a c5340 := h 5339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6310 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6288, some c6280, some c6227, some c6303, some c6306, some c3595, some c6309, some c6308, some c5034, some c5026, some c5022, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6310 : lratChecker f6310 p6310 = .success := by decide +kernel
theorem unsat6310 : Unsatisfiable (PosFin 65) f6310 := by
  apply lratCheckerSound f6310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6310
  · intro a ha; simp [p6310] at ha; subst a; trivial
  · exact checked6310
theorem derived6310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6310 := by
  apply localUnsat_implies_entails f6310 [c6288, c6280, c6227, c6303, c6306, c3595, c6309, c6308, c5034, c5026, c5022] c6310 unsat6310 (by rfl) a
  have h0 : Entails.eval a c6288 := derived6288 a h
  have h1 : Entails.eval a c6280 := derived6280 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6303 := derived6303 a h
  have h4 : Entails.eval a c6306 := derived6306 a h
  have h5 : Entails.eval a c3595 := h 3594 (by decide)
  have h6 : Entails.eval a c6309 := derived6309 a h
  have h7 : Entails.eval a c6308 := derived6308 a h
  have h8 : Entails.eval a c5034 := h 5033 (by decide)
  have h9 : Entails.eval a c5026 := h 5025 (by decide)
  have h10 : Entails.eval a c5022 := h 5021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6311 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6310, some c6280, some c4928, some c4887, some c3904, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6311 : lratChecker f6311 p6311 = .success := by decide +kernel
theorem unsat6311 : Unsatisfiable (PosFin 65) f6311 := by
  apply lratCheckerSound f6311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6311
  · intro a ha; simp [p6311] at ha; subst a; trivial
  · exact checked6311
theorem derived6311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6311 := by
  apply localUnsat_implies_entails f6311 [c6310, c6280, c4928, c4887, c3904] c6311 unsat6311 (by rfl) a
  have h0 : Entails.eval a c6310 := derived6310 a h
  have h1 : Entails.eval a c6280 := derived6280 a h
  have h2 : Entails.eval a c4928 := h 4927 (by decide)
  have h3 : Entails.eval a c4887 := h 4886 (by decide)
  have h4 : Entails.eval a c3904 := h 3903 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6312 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3361, some c2956, some c3164, some c2916, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p6312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6312 : lratChecker f6312 p6312 = .success := by decide +kernel
theorem unsat6312 : Unsatisfiable (PosFin 65) f6312 := by
  apply lratCheckerSound f6312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6312
  · intro a ha; simp [p6312] at ha; subst a; trivial
  · exact checked6312
theorem derived6312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6312 := by
  apply localUnsat_implies_entails f6312 [c3361, c2956, c3164, c2916] c6312 unsat6312 (by rfl) a
  have h0 : Entails.eval a c3361 := h 3360 (by decide)
  have h1 : Entails.eval a c2956 := h 2955 (by decide)
  have h2 : Entails.eval a c3164 := h 3163 (by decide)
  have h3 : Entails.eval a c2916 := h 2915 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6313 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2702, some c3352, some c3284, some c3046, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6313 : lratChecker f6313 p6313 = .success := by decide +kernel
theorem unsat6313 : Unsatisfiable (PosFin 65) f6313 := by
  apply lratCheckerSound f6313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6313
  · intro a ha; simp [p6313] at ha; subst a; trivial
  · exact checked6313
theorem derived6313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6313 := by
  apply localUnsat_implies_entails f6313 [c2702, c3352, c3284, c3046] c6313 unsat6313 (by rfl) a
  have h0 : Entails.eval a c2702 := h 2701 (by decide)
  have h1 : Entails.eval a c3352 := h 3351 (by decide)
  have h2 : Entails.eval a c3284 := h 3283 (by decide)
  have h3 : Entails.eval a c3046 := h 3045 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6314 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨62, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨59, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6313, some c6312, some c3400, some c3096, some c3297, some c3056, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6314 : lratChecker f6314 p6314 = .success := by decide +kernel
theorem unsat6314 : Unsatisfiable (PosFin 65) f6314 := by
  apply lratCheckerSound f6314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6314
  · intro a ha; simp [p6314] at ha; subst a; trivial
  · exact checked6314
theorem derived6314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6314 := by
  apply localUnsat_implies_entails f6314 [c6313, c6312, c3400, c3096, c3297, c3056] c6314 unsat6314 (by rfl) a
  have h0 : Entails.eval a c6313 := derived6313 a h
  have h1 : Entails.eval a c6312 := derived6312 a h
  have h2 : Entails.eval a c3400 := h 3399 (by decide)
  have h3 : Entails.eval a c3096 := h 3095 (by decide)
  have h4 : Entails.eval a c3297 := h 3296 (by decide)
  have h5 : Entails.eval a c3056 := h 3055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6315 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6310, some c6280, some c6283, some c6311, some c4885, some c6288, some c4344, some c4434, some c5333, some c3783, some c6305, some c3888, some c3746, some c5269, some c5782, some c6302, some c3732, some c3733, some c4024, some c3759, some c3737, some c3028, some c3046, some c3054, some c3182, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked6315 : lratChecker f6315 p6315 = .success := by decide +kernel
theorem unsat6315 : Unsatisfiable (PosFin 65) f6315 := by
  apply lratCheckerSound f6315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6315
  · intro a ha; simp [p6315] at ha; subst a; trivial
  · exact checked6315
theorem derived6315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6315 := by
  apply localUnsat_implies_entails f6315 [c6227, c6310, c6280, c6283, c6311, c4885, c6288, c4344, c4434, c5333, c3783, c6305, c3888, c3746, c5269, c5782, c6302, c3732, c3733, c4024, c3759, c3737, c3028, c3046, c3054, c3182] c6315 unsat6315 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6310 := derived6310 a h
  have h2 : Entails.eval a c6280 := derived6280 a h
  have h3 : Entails.eval a c6283 := derived6283 a h
  have h4 : Entails.eval a c6311 := derived6311 a h
  have h5 : Entails.eval a c4885 := h 4884 (by decide)
  have h6 : Entails.eval a c6288 := derived6288 a h
  have h7 : Entails.eval a c4344 := h 4343 (by decide)
  have h8 : Entails.eval a c4434 := h 4433 (by decide)
  have h9 : Entails.eval a c5333 := h 5332 (by decide)
  have h10 : Entails.eval a c3783 := h 3782 (by decide)
  have h11 : Entails.eval a c6305 := derived6305 a h
  have h12 : Entails.eval a c3888 := h 3887 (by decide)
  have h13 : Entails.eval a c3746 := h 3745 (by decide)
  have h14 : Entails.eval a c5269 := h 5268 (by decide)
  have h15 : Entails.eval a c5782 := h 5781 (by decide)
  have h16 : Entails.eval a c6302 := derived6302 a h
  have h17 : Entails.eval a c3732 := h 3731 (by decide)
  have h18 : Entails.eval a c3733 := h 3732 (by decide)
  have h19 : Entails.eval a c4024 := h 4023 (by decide)
  have h20 : Entails.eval a c3759 := h 3758 (by decide)
  have h21 : Entails.eval a c3737 := h 3736 (by decide)
  have h22 : Entails.eval a c3028 := h 3027 (by decide)
  have h23 : Entails.eval a c3046 := h 3045 (by decide)
  have h24 : Entails.eval a c3054 := h 3053 (by decide)
  have h25 : Entails.eval a c3182 := h 3181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6316 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3291, some c3313, some c3384, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6316 : lratChecker f6316 p6316 = .success := by decide +kernel
theorem unsat6316 : Unsatisfiable (PosFin 65) f6316 := by
  apply lratCheckerSound f6316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6316
  · intro a ha; simp [p6316] at ha; subst a; trivial
  · exact checked6316
theorem derived6316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6316 := by
  apply localUnsat_implies_entails f6316 [c3291, c3313, c3384] c6316 unsat6316 (by rfl) a
  have h0 : Entails.eval a c3291 := h 3290 (by decide)
  have h1 : Entails.eval a c3313 := h 3312 (by decide)
  have h2 : Entails.eval a c3384 := h 3383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6317 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6310, some c6280, some c6283, some c6311, some c4885, some c6288, some c4344, some c4434, some c5333, some c3783, some c6305, some c3888, some c3746, some c5269, some c6302, some c3732, some c3733, some c4024, some c3736, some c6315, some c2849, some c2853, some c3197, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked6317 : lratChecker f6317 p6317 = .success := by decide +kernel
theorem unsat6317 : Unsatisfiable (PosFin 65) f6317 := by
  apply lratCheckerSound f6317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6317
  · intro a ha; simp [p6317] at ha; subst a; trivial
  · exact checked6317
theorem derived6317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6317 := by
  apply localUnsat_implies_entails f6317 [c6227, c6310, c6280, c6283, c6311, c4885, c6288, c4344, c4434, c5333, c3783, c6305, c3888, c3746, c5269, c6302, c3732, c3733, c4024, c3736, c6315, c2849, c2853, c3197] c6317 unsat6317 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6310 := derived6310 a h
  have h2 : Entails.eval a c6280 := derived6280 a h
  have h3 : Entails.eval a c6283 := derived6283 a h
  have h4 : Entails.eval a c6311 := derived6311 a h
  have h5 : Entails.eval a c4885 := h 4884 (by decide)
  have h6 : Entails.eval a c6288 := derived6288 a h
  have h7 : Entails.eval a c4344 := h 4343 (by decide)
  have h8 : Entails.eval a c4434 := h 4433 (by decide)
  have h9 : Entails.eval a c5333 := h 5332 (by decide)
  have h10 : Entails.eval a c3783 := h 3782 (by decide)
  have h11 : Entails.eval a c6305 := derived6305 a h
  have h12 : Entails.eval a c3888 := h 3887 (by decide)
  have h13 : Entails.eval a c3746 := h 3745 (by decide)
  have h14 : Entails.eval a c5269 := h 5268 (by decide)
  have h15 : Entails.eval a c6302 := derived6302 a h
  have h16 : Entails.eval a c3732 := h 3731 (by decide)
  have h17 : Entails.eval a c3733 := h 3732 (by decide)
  have h18 : Entails.eval a c4024 := h 4023 (by decide)
  have h19 : Entails.eval a c3736 := h 3735 (by decide)
  have h20 : Entails.eval a c6315 := derived6315 a h
  have h21 : Entails.eval a c2849 := h 2848 (by decide)
  have h22 : Entails.eval a c2853 := h 2852 (by decide)
  have h23 : Entails.eval a c3197 := h 3196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6318 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6288, some c6280, some c6310, some c6283, some c6311, some c6227, some c4885, some c4344, some c4434, some c5333, some c3783, some c6305, some c3732, some c3746, some c3888, some c3737, some c3733, some c4621, some c6302, some c5269, some c3759, some c3736, some c4024, some c5648, some c4397, some c5782, some c6314, some c6317, some c6316, some c6312, some c2702, some c2751, some c2773, some c3069, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked6318 : lratChecker f6318 p6318 = .success := by decide +kernel
theorem unsat6318 : Unsatisfiable (PosFin 65) f6318 := by
  apply lratCheckerSound f6318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6318
  · intro a ha; simp [p6318] at ha; subst a; trivial
  · exact checked6318
theorem derived6318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6318 := by
  apply localUnsat_implies_entails f6318 [c6288, c6280, c6310, c6283, c6311, c6227, c4885, c4344, c4434, c5333, c3783, c6305, c3732, c3746, c3888, c3737, c3733, c4621, c6302, c5269, c3759, c3736, c4024, c5648, c4397, c5782, c6314, c6317, c6316, c6312, c2702, c2751, c2773, c3069] c6318 unsat6318 (by rfl) a
  have h0 : Entails.eval a c6288 := derived6288 a h
  have h1 : Entails.eval a c6280 := derived6280 a h
  have h2 : Entails.eval a c6310 := derived6310 a h
  have h3 : Entails.eval a c6283 := derived6283 a h
  have h4 : Entails.eval a c6311 := derived6311 a h
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c4885 := h 4884 (by decide)
  have h7 : Entails.eval a c4344 := h 4343 (by decide)
  have h8 : Entails.eval a c4434 := h 4433 (by decide)
  have h9 : Entails.eval a c5333 := h 5332 (by decide)
  have h10 : Entails.eval a c3783 := h 3782 (by decide)
  have h11 : Entails.eval a c6305 := derived6305 a h
  have h12 : Entails.eval a c3732 := h 3731 (by decide)
  have h13 : Entails.eval a c3746 := h 3745 (by decide)
  have h14 : Entails.eval a c3888 := h 3887 (by decide)
  have h15 : Entails.eval a c3737 := h 3736 (by decide)
  have h16 : Entails.eval a c3733 := h 3732 (by decide)
  have h17 : Entails.eval a c4621 := h 4620 (by decide)
  have h18 : Entails.eval a c6302 := derived6302 a h
  have h19 : Entails.eval a c5269 := h 5268 (by decide)
  have h20 : Entails.eval a c3759 := h 3758 (by decide)
  have h21 : Entails.eval a c3736 := h 3735 (by decide)
  have h22 : Entails.eval a c4024 := h 4023 (by decide)
  have h23 : Entails.eval a c5648 := h 5647 (by decide)
  have h24 : Entails.eval a c4397 := h 4396 (by decide)
  have h25 : Entails.eval a c5782 := h 5781 (by decide)
  have h26 : Entails.eval a c6314 := derived6314 a h
  have h27 : Entails.eval a c6317 := derived6317 a h
  have h28 : Entails.eval a c6316 := derived6316 a h
  have h29 : Entails.eval a c6312 := derived6312 a h
  have h30 : Entails.eval a c2702 := h 2701 (by decide)
  have h31 : Entails.eval a c2751 := h 2750 (by decide)
  have h32 : Entails.eval a c2773 := h 2772 (by decide)
  have h33 : Entails.eval a c3069 := h 3068 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6319 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨49, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2751, some c2773, some c3284, some c3330, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6319 : lratChecker f6319 p6319 = .success := by decide +kernel
theorem unsat6319 : Unsatisfiable (PosFin 65) f6319 := by
  apply lratCheckerSound f6319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6319
  · intro a ha; simp [p6319] at ha; subst a; trivial
  · exact checked6319
theorem derived6319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6319 := by
  apply localUnsat_implies_entails f6319 [c2751, c2773, c3284, c3330] c6319 unsat6319 (by rfl) a
  have h0 : Entails.eval a c2751 := h 2750 (by decide)
  have h1 : Entails.eval a c2773 := h 2772 (by decide)
  have h2 : Entails.eval a c3284 := h 3283 (by decide)
  have h3 : Entails.eval a c3330 := h 3329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6320 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨34, by decide⟩, false), (⟨54, by decide⟩, false), (⟨59, by decide⟩, false), (⟨49, by decide⟩, true), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6319, some c6312, some c3297, some c3291, some c3313, some c3383, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6320 : lratChecker f6320 p6320 = .success := by decide +kernel
theorem unsat6320 : Unsatisfiable (PosFin 65) f6320 := by
  apply lratCheckerSound f6320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6320
  · intro a ha; simp [p6320] at ha; subst a; trivial
  · exact checked6320
theorem derived6320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6320 := by
  apply localUnsat_implies_entails f6320 [c6319, c6312, c3297, c3291, c3313, c3383] c6320 unsat6320 (by rfl) a
  have h0 : Entails.eval a c6319 := derived6319 a h
  have h1 : Entails.eval a c6312 := derived6312 a h
  have h2 : Entails.eval a c3297 := h 3296 (by decide)
  have h3 : Entails.eval a c3291 := h 3290 (by decide)
  have h4 : Entails.eval a c3313 := h 3312 (by decide)
  have h5 : Entails.eval a c3383 := h 3382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6321 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3058, some c3051, some c3028, some c3184, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6321 : lratChecker f6321 p6321 = .success := by decide +kernel
theorem unsat6321 : Unsatisfiable (PosFin 65) f6321 := by
  apply lratCheckerSound f6321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6321
  · intro a ha; simp [p6321] at ha; subst a; trivial
  · exact checked6321
theorem derived6321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6321 := by
  apply localUnsat_implies_entails f6321 [c3058, c3051, c3028, c3184] c6321 unsat6321 (by rfl) a
  have h0 : Entails.eval a c3058 := h 3057 (by decide)
  have h1 : Entails.eval a c3051 := h 3050 (by decide)
  have h2 : Entails.eval a c3028 := h 3027 (by decide)
  have h3 : Entails.eval a c3184 := h 3183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6322 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6280, some c6288, some c6310, some c6283, some c6311, some c4344, some c4885, some c4434, some c5333, some c3783, some c6305, some c6318, some c5441, some c5439, some c4940, some c5290, some c5265, some c5279, some c4930, some c4918, some c6302, some c4158, some c5782, some c4397, some c6320, some c6321, some c2851, some c2855, some c3197, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6322 : lratChecker f6322 p6322 = .success := by decide +kernel
theorem unsat6322 : Unsatisfiable (PosFin 65) f6322 := by
  apply lratCheckerSound f6322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6322
  · intro a ha; simp [p6322] at ha; subst a; trivial
  · exact checked6322
theorem derived6322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6322 := by
  apply localUnsat_implies_entails f6322 [c6227, c6280, c6288, c6310, c6283, c6311, c4344, c4885, c4434, c5333, c3783, c6305, c6318, c5441, c5439, c4940, c5290, c5265, c5279, c4930, c4918, c6302, c4158, c5782, c4397, c6320, c6321, c2851, c2855, c3197] c6322 unsat6322 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6280 := derived6280 a h
  have h2 : Entails.eval a c6288 := derived6288 a h
  have h3 : Entails.eval a c6310 := derived6310 a h
  have h4 : Entails.eval a c6283 := derived6283 a h
  have h5 : Entails.eval a c6311 := derived6311 a h
  have h6 : Entails.eval a c4344 := h 4343 (by decide)
  have h7 : Entails.eval a c4885 := h 4884 (by decide)
  have h8 : Entails.eval a c4434 := h 4433 (by decide)
  have h9 : Entails.eval a c5333 := h 5332 (by decide)
  have h10 : Entails.eval a c3783 := h 3782 (by decide)
  have h11 : Entails.eval a c6305 := derived6305 a h
  have h12 : Entails.eval a c6318 := derived6318 a h
  have h13 : Entails.eval a c5441 := h 5440 (by decide)
  have h14 : Entails.eval a c5439 := h 5438 (by decide)
  have h15 : Entails.eval a c4940 := h 4939 (by decide)
  have h16 : Entails.eval a c5290 := h 5289 (by decide)
  have h17 : Entails.eval a c5265 := h 5264 (by decide)
  have h18 : Entails.eval a c5279 := h 5278 (by decide)
  have h19 : Entails.eval a c4930 := h 4929 (by decide)
  have h20 : Entails.eval a c4918 := h 4917 (by decide)
  have h21 : Entails.eval a c6302 := derived6302 a h
  have h22 : Entails.eval a c4158 := h 4157 (by decide)
  have h23 : Entails.eval a c5782 := h 5781 (by decide)
  have h24 : Entails.eval a c4397 := h 4396 (by decide)
  have h25 : Entails.eval a c6320 := derived6320 a h
  have h26 : Entails.eval a c6321 := derived6321 a h
  have h27 : Entails.eval a c2851 := h 2850 (by decide)
  have h28 : Entails.eval a c2855 := h 2854 (by decide)
  have h29 : Entails.eval a c3197 := h 3196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6323 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6322, some c6227, some c3432, some c3442, some c3433, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6323 : lratChecker f6323 p6323 = .success := by decide +kernel
theorem unsat6323 : Unsatisfiable (PosFin 65) f6323 := by
  apply lratCheckerSound f6323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6323
  · intro a ha; simp [p6323] at ha; subst a; trivial
  · exact checked6323
theorem derived6323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6323 := by
  apply localUnsat_implies_entails f6323 [c6322, c6227, c3432, c3442, c3433] c6323 unsat6323 (by rfl) a
  have h0 : Entails.eval a c6322 := derived6322 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c3432 := h 3431 (by decide)
  have h3 : Entails.eval a c3442 := h 3441 (by decide)
  have h4 : Entails.eval a c3433 := h 3432 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6324 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨58, by decide⟩, true), (⟨36, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3491, some c3467, some c4843, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6324 : lratChecker f6324 p6324 = .success := by decide +kernel
theorem unsat6324 : Unsatisfiable (PosFin 65) f6324 := by
  apply lratCheckerSound f6324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6324
  · intro a ha; simp [p6324] at ha; subst a; trivial
  · exact checked6324
theorem derived6324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6324 := by
  apply localUnsat_implies_entails f6324 [c3491, c3467, c4843] c6324 unsat6324 (by rfl) a
  have h0 : Entails.eval a c3491 := h 3490 (by decide)
  have h1 : Entails.eval a c3467 := h 3466 (by decide)
  have h2 : Entails.eval a c4843 := h 4842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6325 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6323, some c6322, some c3490, some c3466, some c4842, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6325 : lratChecker f6325 p6325 = .success := by decide +kernel
theorem unsat6325 : Unsatisfiable (PosFin 65) f6325 := by
  apply lratCheckerSound f6325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6325
  · intro a ha; simp [p6325] at ha; subst a; trivial
  · exact checked6325
theorem derived6325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6325 := by
  apply localUnsat_implies_entails f6325 [c6323, c6322, c3490, c3466, c4842] c6325 unsat6325 (by rfl) a
  have h0 : Entails.eval a c6323 := derived6323 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c3490 := h 3489 (by decide)
  have h3 : Entails.eval a c3466 := h 3465 (by decide)
  have h4 : Entails.eval a c4842 := h 4841 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6326 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6322, some c6227, some c6323, some c6325, some c6324, some c3498, some c3473, some c4845, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6326 : lratChecker f6326 p6326 = .success := by decide +kernel
theorem unsat6326 : Unsatisfiable (PosFin 65) f6326 := by
  apply lratCheckerSound f6326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6326
  · intro a ha; simp [p6326] at ha; subst a; trivial
  · exact checked6326
theorem derived6326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6326 := by
  apply localUnsat_implies_entails f6326 [c6322, c6227, c6323, c6325, c6324, c3498, c3473, c4845] c6326 unsat6326 (by rfl) a
  have h0 : Entails.eval a c6322 := derived6322 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6323 := derived6323 a h
  have h3 : Entails.eval a c6325 := derived6325 a h
  have h4 : Entails.eval a c6324 := derived6324 a h
  have h5 : Entails.eval a c3498 := h 3497 (by decide)
  have h6 : Entails.eval a c3473 := h 3472 (by decide)
  have h7 : Entails.eval a c4845 := h 4844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6327 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨58, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c4272, some c4087, some c5454, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6327 : lratChecker f6327 p6327 = .success := by decide +kernel
theorem unsat6327 : Unsatisfiable (PosFin 65) f6327 := by
  apply lratCheckerSound f6327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6327
  · intro a ha; simp [p6327] at ha; subst a; trivial
  · exact checked6327
theorem derived6327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6327 := by
  apply localUnsat_implies_entails f6327 [c6326, c4272, c4087, c5454] c6327 unsat6327 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c4272 := h 4271 (by decide)
  have h2 : Entails.eval a c4087 := h 4086 (by decide)
  have h3 : Entails.eval a c5454 := h 5453 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6328 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4804, some c6265, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p6328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6328 : lratChecker f6328 p6328 = .success := by decide +kernel
theorem unsat6328 : Unsatisfiable (PosFin 65) f6328 := by
  apply lratCheckerSound f6328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6328
  · intro a ha; simp [p6328] at ha; subst a; trivial
  · exact checked6328
theorem derived6328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6328 := by
  apply localUnsat_implies_entails f6328 [c4804, c6265] c6328 unsat6328 (by rfl) a
  have h0 : Entails.eval a c4804 := h 4803 (by decide)
  have h1 : Entails.eval a c6265 := derived6265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6329 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨36, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6322, some c6327, some c3847, some c6328, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6329 : lratChecker f6329 p6329 = .success := by decide +kernel
theorem unsat6329 : Unsatisfiable (PosFin 65) f6329 := by
  apply lratCheckerSound f6329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6329
  · intro a ha; simp [p6329] at ha; subst a; trivial
  · exact checked6329
theorem derived6329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6329 := by
  apply localUnsat_implies_entails f6329 [c6322, c6327, c3847, c6328] c6329 unsat6329 (by rfl) a
  have h0 : Entails.eval a c6322 := derived6322 a h
  have h1 : Entails.eval a c6327 := derived6327 a h
  have h2 : Entails.eval a c3847 := h 3846 (by decide)
  have h3 : Entails.eval a c6328 := derived6328 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6330 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨58, by decide⟩, true), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6265, some c4799, some c4800, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6330 : lratChecker f6330 p6330 = .success := by decide +kernel
theorem unsat6330 : Unsatisfiable (PosFin 65) f6330 := by
  apply lratCheckerSound f6330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6330
  · intro a ha; simp [p6330] at ha; subst a; trivial
  · exact checked6330
theorem derived6330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6330 := by
  apply localUnsat_implies_entails f6330 [c6227, c6265, c4799, c4800] c6330 unsat6330 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6265 := derived6265 a h
  have h2 : Entails.eval a c4799 := h 4798 (by decide)
  have h3 : Entails.eval a c4800 := h 4799 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6331 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6329, some c6330, some c6326, some c6322, some c6227, some c3841, some c4740, some c4194, some c4269, some c4084, some c5585, some c5440, some c5441, some c5267, some c4822, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6331 : lratChecker f6331 p6331 = .success := by decide +kernel
theorem unsat6331 : Unsatisfiable (PosFin 65) f6331 := by
  apply lratCheckerSound f6331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6331
  · intro a ha; simp [p6331] at ha; subst a; trivial
  · exact checked6331
theorem derived6331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6331 := by
  apply localUnsat_implies_entails f6331 [c6329, c6330, c6326, c6322, c6227, c3841, c4740, c4194, c4269, c4084, c5585, c5440, c5441, c5267, c4822] c6331 unsat6331 (by rfl) a
  have h0 : Entails.eval a c6329 := derived6329 a h
  have h1 : Entails.eval a c6330 := derived6330 a h
  have h2 : Entails.eval a c6326 := derived6326 a h
  have h3 : Entails.eval a c6322 := derived6322 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c3841 := h 3840 (by decide)
  have h6 : Entails.eval a c4740 := h 4739 (by decide)
  have h7 : Entails.eval a c4194 := h 4193 (by decide)
  have h8 : Entails.eval a c4269 := h 4268 (by decide)
  have h9 : Entails.eval a c4084 := h 4083 (by decide)
  have h10 : Entails.eval a c5585 := h 5584 (by decide)
  have h11 : Entails.eval a c5440 := h 5439 (by decide)
  have h12 : Entails.eval a c5441 := h 5440 (by decide)
  have h13 : Entails.eval a c5267 := h 5266 (by decide)
  have h14 : Entails.eval a c4822 := h 4821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6332 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6329, some c6330, some c6326, some c6322, some c6331, some c4165, some c3812, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6332 : lratChecker f6332 p6332 = .success := by decide +kernel
theorem unsat6332 : Unsatisfiable (PosFin 65) f6332 := by
  apply lratCheckerSound f6332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6332
  · intro a ha; simp [p6332] at ha; subst a; trivial
  · exact checked6332
theorem derived6332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6332 := by
  apply localUnsat_implies_entails f6332 [c6329, c6330, c6326, c6322, c6331, c4165, c3812] c6332 unsat6332 (by rfl) a
  have h0 : Entails.eval a c6329 := derived6329 a h
  have h1 : Entails.eval a c6330 := derived6330 a h
  have h2 : Entails.eval a c6326 := derived6326 a h
  have h3 : Entails.eval a c6322 := derived6322 a h
  have h4 : Entails.eval a c6331 := derived6331 a h
  have h5 : Entails.eval a c4165 := h 4164 (by decide)
  have h6 : Entails.eval a c3812 := h 3811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6333 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6322, some c3812, some c3840, some c4866, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6333 : lratChecker f6333 p6333 = .success := by decide +kernel
theorem unsat6333 : Unsatisfiable (PosFin 65) f6333 := by
  apply lratCheckerSound f6333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6333
  · intro a ha; simp [p6333] at ha; subst a; trivial
  · exact checked6333
theorem derived6333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6333 := by
  apply localUnsat_implies_entails f6333 [c6322, c3812, c3840, c4866] c6333 unsat6333 (by rfl) a
  have h0 : Entails.eval a c6322 := derived6322 a h
  have h1 : Entails.eval a c3812 := h 3811 (by decide)
  have h2 : Entails.eval a c3840 := h 3839 (by decide)
  have h3 : Entails.eval a c4866 := h 4865 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6334 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c6322, some c6227, some c6329, some c6330, some c6332, some c6333, some c3841, some c4269, some c4084, some c5333, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6334 : lratChecker f6334 p6334 = .success := by decide +kernel
theorem unsat6334 : Unsatisfiable (PosFin 65) f6334 := by
  apply lratCheckerSound f6334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6334
  · intro a ha; simp [p6334] at ha; subst a; trivial
  · exact checked6334
theorem derived6334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6334 := by
  apply localUnsat_implies_entails f6334 [c6326, c6322, c6227, c6329, c6330, c6332, c6333, c3841, c4269, c4084, c5333] c6334 unsat6334 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6329 := derived6329 a h
  have h4 : Entails.eval a c6330 := derived6330 a h
  have h5 : Entails.eval a c6332 := derived6332 a h
  have h6 : Entails.eval a c6333 := derived6333 a h
  have h7 : Entails.eval a c3841 := h 3840 (by decide)
  have h8 : Entails.eval a c4269 := h 4268 (by decide)
  have h9 : Entails.eval a c4084 := h 4083 (by decide)
  have h10 : Entails.eval a c5333 := h 5332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6335 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6334, some c6326, some c6322, some c6227, some c3513, some c3841, some c3959, some c4269, some c5444, some c5440, some c4885, some c5441, some c5380, some c5785, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6335 : lratChecker f6335 p6335 = .success := by decide +kernel
theorem unsat6335 : Unsatisfiable (PosFin 65) f6335 := by
  apply lratCheckerSound f6335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6335
  · intro a ha; simp [p6335] at ha; subst a; trivial
  · exact checked6335
theorem derived6335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6335 := by
  apply localUnsat_implies_entails f6335 [c6334, c6326, c6322, c6227, c3513, c3841, c3959, c4269, c5444, c5440, c4885, c5441, c5380, c5785] c6335 unsat6335 (by rfl) a
  have h0 : Entails.eval a c6334 := derived6334 a h
  have h1 : Entails.eval a c6326 := derived6326 a h
  have h2 : Entails.eval a c6322 := derived6322 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c3513 := h 3512 (by decide)
  have h5 : Entails.eval a c3841 := h 3840 (by decide)
  have h6 : Entails.eval a c3959 := h 3958 (by decide)
  have h7 : Entails.eval a c4269 := h 4268 (by decide)
  have h8 : Entails.eval a c5444 := h 5443 (by decide)
  have h9 : Entails.eval a c5440 := h 5439 (by decide)
  have h10 : Entails.eval a c4885 := h 4884 (by decide)
  have h11 : Entails.eval a c5441 := h 5440 (by decide)
  have h12 : Entails.eval a c5380 := h 5379 (by decide)
  have h13 : Entails.eval a c5785 := h 5784 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6336 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6322, some c6327, some c3847, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6336 : lratChecker f6336 p6336 = .success := by decide +kernel
theorem unsat6336 : Unsatisfiable (PosFin 65) f6336 := by
  apply lratCheckerSound f6336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6336
  · intro a ha; simp [p6336] at ha; subst a; trivial
  · exact checked6336
theorem derived6336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6336 := by
  apply localUnsat_implies_entails f6336 [c6322, c6327, c3847] c6336 unsat6336 (by rfl) a
  have h0 : Entails.eval a c6322 := derived6322 a h
  have h1 : Entails.eval a c6327 := derived6327 a h
  have h2 : Entails.eval a c3847 := h 3846 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6337 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6334, some c6326, some c6322, some c6336, some c6335, some c6283, some c3840, some c4266, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6337 : lratChecker f6337 p6337 = .success := by decide +kernel
theorem unsat6337 : Unsatisfiable (PosFin 65) f6337 := by
  apply lratCheckerSound f6337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6337
  · intro a ha; simp [p6337] at ha; subst a; trivial
  · exact checked6337
theorem derived6337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6337 := by
  apply localUnsat_implies_entails f6337 [c6334, c6326, c6322, c6336, c6335, c6283, c3840, c4266] c6337 unsat6337 (by rfl) a
  have h0 : Entails.eval a c6334 := derived6334 a h
  have h1 : Entails.eval a c6326 := derived6326 a h
  have h2 : Entails.eval a c6322 := derived6322 a h
  have h3 : Entails.eval a c6336 := derived6336 a h
  have h4 : Entails.eval a c6335 := derived6335 a h
  have h5 : Entails.eval a c6283 := derived6283 a h
  have h6 : Entails.eval a c3840 := h 3839 (by decide)
  have h7 : Entails.eval a c4266 := h 4265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6338 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6337, some c6334, some c6326, some c6322, some c3511, some c6283, some c4521, some c4266, some c5825, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6338 : lratChecker f6338 p6338 = .success := by decide +kernel
theorem unsat6338 : Unsatisfiable (PosFin 65) f6338 := by
  apply lratCheckerSound f6338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6338
  · intro a ha; simp [p6338] at ha; subst a; trivial
  · exact checked6338
theorem derived6338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6338 := by
  apply localUnsat_implies_entails f6338 [c6337, c6334, c6326, c6322, c3511, c6283, c4521, c4266, c5825] c6338 unsat6338 (by rfl) a
  have h0 : Entails.eval a c6337 := derived6337 a h
  have h1 : Entails.eval a c6334 := derived6334 a h
  have h2 : Entails.eval a c6326 := derived6326 a h
  have h3 : Entails.eval a c6322 := derived6322 a h
  have h4 : Entails.eval a c3511 := h 3510 (by decide)
  have h5 : Entails.eval a c6283 := derived6283 a h
  have h6 : Entails.eval a c4521 := h 4520 (by decide)
  have h7 : Entails.eval a c4266 := h 4265 (by decide)
  have h8 : Entails.eval a c5825 := h 5824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6339 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6322, some c6227, some c3880, some c5830, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6339 : lratChecker f6339 p6339 = .success := by decide +kernel
theorem unsat6339 : Unsatisfiable (PosFin 65) f6339 := by
  apply lratCheckerSound f6339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6339
  · intro a ha; simp [p6339] at ha; subst a; trivial
  · exact checked6339
theorem derived6339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6339 := by
  apply localUnsat_implies_entails f6339 [c6322, c6227, c3880, c5830] c6339 unsat6339 (by rfl) a
  have h0 : Entails.eval a c6322 := derived6322 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c3880 := h 3879 (by decide)
  have h3 : Entails.eval a c5830 := h 5829 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6340 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4522, some c4526, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6340 : lratChecker f6340 p6340 = .success := by decide +kernel
theorem unsat6340 : Unsatisfiable (PosFin 65) f6340 := by
  apply lratCheckerSound f6340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6340
  · intro a ha; simp [p6340] at ha; subst a; trivial
  · exact checked6340
theorem derived6340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6340 := by
  apply localUnsat_implies_entails f6340 [c6227, c4522, c4526] c6340 unsat6340 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4522 := h 4521 (by decide)
  have h2 : Entails.eval a c4526 := h 4525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6341 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6338, some c6337, some c6334, some c6322, some c6227, some c6339, some c6340, some c3569, some c3520, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6341 : lratChecker f6341 p6341 = .success := by decide +kernel
theorem unsat6341 : Unsatisfiable (PosFin 65) f6341 := by
  apply lratCheckerSound f6341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6341
  · intro a ha; simp [p6341] at ha; subst a; trivial
  · exact checked6341
theorem derived6341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6341 := by
  apply localUnsat_implies_entails f6341 [c6338, c6337, c6334, c6322, c6227, c6339, c6340, c3569, c3520] c6341 unsat6341 (by rfl) a
  have h0 : Entails.eval a c6338 := derived6338 a h
  have h1 : Entails.eval a c6337 := derived6337 a h
  have h2 : Entails.eval a c6334 := derived6334 a h
  have h3 : Entails.eval a c6322 := derived6322 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6339 := derived6339 a h
  have h6 : Entails.eval a c6340 := derived6340 a h
  have h7 : Entails.eval a c3569 := h 3568 (by decide)
  have h8 : Entails.eval a c3520 := h 3519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6342 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c6322, some c6227, some c6334, some c6337, some c6338, some c6341, some c6327, some c3513, some c3959, some c4522, some c4269, some c5429, some c5427, some c5441, some c5382, some c4236, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6342 : lratChecker f6342 p6342 = .success := by decide +kernel
theorem unsat6342 : Unsatisfiable (PosFin 65) f6342 := by
  apply lratCheckerSound f6342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6342
  · intro a ha; simp [p6342] at ha; subst a; trivial
  · exact checked6342
theorem derived6342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6342 := by
  apply localUnsat_implies_entails f6342 [c6326, c6322, c6227, c6334, c6337, c6338, c6341, c6327, c3513, c3959, c4522, c4269, c5429, c5427, c5441, c5382, c4236] c6342 unsat6342 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6334 := derived6334 a h
  have h4 : Entails.eval a c6337 := derived6337 a h
  have h5 : Entails.eval a c6338 := derived6338 a h
  have h6 : Entails.eval a c6341 := derived6341 a h
  have h7 : Entails.eval a c6327 := derived6327 a h
  have h8 : Entails.eval a c3513 := h 3512 (by decide)
  have h9 : Entails.eval a c3959 := h 3958 (by decide)
  have h10 : Entails.eval a c4522 := h 4521 (by decide)
  have h11 : Entails.eval a c4269 := h 4268 (by decide)
  have h12 : Entails.eval a c5429 := h 5428 (by decide)
  have h13 : Entails.eval a c5427 := h 5426 (by decide)
  have h14 : Entails.eval a c5441 := h 5440 (by decide)
  have h15 : Entails.eval a c5382 := h 5381 (by decide)
  have h16 : Entails.eval a c4236 := h 4235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6343 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨53, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6342, some c6326, some c6227, some c6327, some c4269, some c4084, some c5439, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6343 : lratChecker f6343 p6343 = .success := by decide +kernel
theorem unsat6343 : Unsatisfiable (PosFin 65) f6343 := by
  apply lratCheckerSound f6343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6343
  · intro a ha; simp [p6343] at ha; subst a; trivial
  · exact checked6343
theorem derived6343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6343 := by
  apply localUnsat_implies_entails f6343 [c6342, c6326, c6227, c6327, c4269, c4084, c5439] c6343 unsat6343 (by rfl) a
  have h0 : Entails.eval a c6342 := derived6342 a h
  have h1 : Entails.eval a c6326 := derived6326 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6327 := derived6327 a h
  have h4 : Entails.eval a c4269 := h 4268 (by decide)
  have h5 : Entails.eval a c4084 := h 4083 (by decide)
  have h6 : Entails.eval a c5439 := h 5438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6344 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3826, some c3560, some c4522, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6344 : lratChecker f6344 p6344 = .success := by decide +kernel
theorem unsat6344 : Unsatisfiable (PosFin 65) f6344 := by
  apply lratCheckerSound f6344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6344
  · intro a ha; simp [p6344] at ha; subst a; trivial
  · exact checked6344
theorem derived6344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6344 := by
  apply localUnsat_implies_entails f6344 [c3826, c3560, c4522] c6344 unsat6344 (by rfl) a
  have h0 : Entails.eval a c3826 := h 3825 (by decide)
  have h1 : Entails.eval a c3560 := h 3559 (by decide)
  have h2 : Entails.eval a c4522 := h 4521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6345 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6342, some c6322, some c6227, some c6343, some c6339, some c6344, some c3847, some c3575, some c4526, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6345 : lratChecker f6345 p6345 = .success := by decide +kernel
theorem unsat6345 : Unsatisfiable (PosFin 65) f6345 := by
  apply lratCheckerSound f6345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6345
  · intro a ha; simp [p6345] at ha; subst a; trivial
  · exact checked6345
theorem derived6345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6345 := by
  apply localUnsat_implies_entails f6345 [c6342, c6322, c6227, c6343, c6339, c6344, c3847, c3575, c4526] c6345 unsat6345 (by rfl) a
  have h0 : Entails.eval a c6342 := derived6342 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6343 := derived6343 a h
  have h4 : Entails.eval a c6339 := derived6339 a h
  have h5 : Entails.eval a c6344 := derived6344 a h
  have h6 : Entails.eval a c3847 := h 3846 (by decide)
  have h7 : Entails.eval a c3575 := h 3574 (by decide)
  have h8 : Entails.eval a c4526 := h 4525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6346 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3567, some c3840, some c3878, some c4521, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6346 : lratChecker f6346 p6346 = .success := by decide +kernel
theorem unsat6346 : Unsatisfiable (PosFin 65) f6346 := by
  apply lratCheckerSound f6346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6346
  · intro a ha; simp [p6346] at ha; subst a; trivial
  · exact checked6346
theorem derived6346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6346 := by
  apply localUnsat_implies_entails f6346 [c3567, c3840, c3878, c4521] c6346 unsat6346 (by rfl) a
  have h0 : Entails.eval a c3567 := h 3566 (by decide)
  have h1 : Entails.eval a c3840 := h 3839 (by decide)
  have h2 : Entails.eval a c3878 := h 3877 (by decide)
  have h3 : Entails.eval a c4521 := h 4520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6347 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c6322, some c6345, some c6346, some c4266, some c4083, some c5451, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6347 : lratChecker f6347 p6347 = .success := by decide +kernel
theorem unsat6347 : Unsatisfiable (PosFin 65) f6347 := by
  apply lratCheckerSound f6347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6347
  · intro a ha; simp [p6347] at ha; subst a; trivial
  · exact checked6347
theorem derived6347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6347 := by
  apply localUnsat_implies_entails f6347 [c6326, c6322, c6345, c6346, c4266, c4083, c5451] c6347 unsat6347 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c6345 := derived6345 a h
  have h3 : Entails.eval a c6346 := derived6346 a h
  have h4 : Entails.eval a c4266 := h 4265 (by decide)
  have h5 : Entails.eval a c4083 := h 4082 (by decide)
  have h6 : Entails.eval a c5451 := h 5450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6348 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false), (⟨34, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4266, some c4083, some c4243, some c5387, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6348 : lratChecker f6348 p6348 = .success := by decide +kernel
theorem unsat6348 : Unsatisfiable (PosFin 65) f6348 := by
  apply lratCheckerSound f6348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6348
  · intro a ha; simp [p6348] at ha; subst a; trivial
  · exact checked6348
theorem derived6348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6348 := by
  apply localUnsat_implies_entails f6348 [c4266, c4083, c4243, c5387] c6348 unsat6348 (by rfl) a
  have h0 : Entails.eval a c4266 := h 4265 (by decide)
  have h1 : Entails.eval a c4083 := h 4082 (by decide)
  have h2 : Entails.eval a c4243 := h 4242 (by decide)
  have h3 : Entails.eval a c5387 := h 5386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6349 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c6322, some c6346, some c6348, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6349 : lratChecker f6349 p6349 = .success := by decide +kernel
theorem unsat6349 : Unsatisfiable (PosFin 65) f6349 := by
  apply lratCheckerSound f6349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6349
  · intro a ha; simp [p6349] at ha; subst a; trivial
  · exact checked6349
theorem derived6349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6349 := by
  apply localUnsat_implies_entails f6349 [c6326, c6322, c6346, c6348] c6349 unsat6349 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c6346 := derived6346 a h
  have h3 : Entails.eval a c6348 := derived6348 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6350 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6349, some c6227, some c5335, some c5333, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6350 : lratChecker f6350 p6350 = .success := by decide +kernel
theorem unsat6350 : Unsatisfiable (PosFin 65) f6350 := by
  apply lratCheckerSound f6350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6350
  · intro a ha; simp [p6350] at ha; subst a; trivial
  · exact checked6350
theorem derived6350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6350 := by
  apply localUnsat_implies_entails f6350 [c6349, c6227, c5335, c5333] c6350 unsat6350 (by rfl) a
  have h0 : Entails.eval a c6349 := derived6349 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5335 := h 5334 (by decide)
  have h3 : Entails.eval a c5333 := h 5332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6351 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨44, by decide⟩, true), (⟨56, by decide⟩, true), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨60, by decide⟩, false), (⟨52, by decide⟩, true), (⟨59, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨47, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5947, some c5761, some c4633, some c5517, some c3508, some c4687, some c5928, some c6302, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6351 : lratChecker f6351 p6351 = .success := by decide +kernel
theorem unsat6351 : Unsatisfiable (PosFin 65) f6351 := by
  apply lratCheckerSound f6351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6351
  · intro a ha; simp [p6351] at ha; subst a; trivial
  · exact checked6351
theorem derived6351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6351 := by
  apply localUnsat_implies_entails f6351 [c5947, c5761, c4633, c5517, c3508, c4687, c5928, c6302] c6351 unsat6351 (by rfl) a
  have h0 : Entails.eval a c5947 := derived5947 a h
  have h1 : Entails.eval a c5761 := h 5760 (by decide)
  have h2 : Entails.eval a c4633 := h 4632 (by decide)
  have h3 : Entails.eval a c5517 := h 5516 (by decide)
  have h4 : Entails.eval a c3508 := h 3507 (by decide)
  have h5 : Entails.eval a c4687 := h 4686 (by decide)
  have h6 : Entails.eval a c5928 := derived5928 a h
  have h7 : Entails.eval a c6302 := derived6302 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6352 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨57, by decide⟩, false), (⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨60, by decide⟩, false), (⟨52, by decide⟩, true), (⟨59, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c5930, some c6347, some c6322, some c6227, some c6351, some c5900, some c3940, some c4359, some c4683, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6352 : lratChecker f6352 p6352 = .success := by decide +kernel
theorem unsat6352 : Unsatisfiable (PosFin 65) f6352 := by
  apply lratCheckerSound f6352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6352
  · intro a ha; simp [p6352] at ha; subst a; trivial
  · exact checked6352
theorem derived6352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6352 := by
  apply localUnsat_implies_entails f6352 [c6326, c5930, c6347, c6322, c6227, c6351, c5900, c3940, c4359, c4683] c6352 unsat6352 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c5930 := derived5930 a h
  have h2 : Entails.eval a c6347 := derived6347 a h
  have h3 : Entails.eval a c6322 := derived6322 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6351 := derived6351 a h
  have h6 : Entails.eval a c5900 := derived5900 a h
  have h7 : Entails.eval a c3940 := h 3939 (by decide)
  have h8 : Entails.eval a c4359 := h 4358 (by decide)
  have h9 : Entails.eval a c4683 := h 4682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6353 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨35, by decide⟩, false), (⟨58, by decide⟩, false), (⟨44, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, false), (⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2698, some c2756, some c3036, some c2949, some c2718, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6353 : lratChecker f6353 p6353 = .success := by decide +kernel
theorem unsat6353 : Unsatisfiable (PosFin 65) f6353 := by
  apply lratCheckerSound f6353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6353
  · intro a ha; simp [p6353] at ha; subst a; trivial
  · exact checked6353
theorem derived6353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6353 := by
  apply localUnsat_implies_entails f6353 [c2698, c2756, c3036, c2949, c2718] c6353 unsat6353 (by rfl) a
  have h0 : Entails.eval a c2698 := h 2697 (by decide)
  have h1 : Entails.eval a c2756 := h 2755 (by decide)
  have h2 : Entails.eval a c3036 := h 3035 (by decide)
  have h3 : Entails.eval a c2949 := h 2948 (by decide)
  have h4 : Entails.eval a c2718 := h 2717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6354 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨58, by decide⟩, false), (⟨57, by decide⟩, false), (⟨48, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2715, some c2718, some c3420, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6354 : lratChecker f6354 p6354 = .success := by decide +kernel
theorem unsat6354 : Unsatisfiable (PosFin 65) f6354 := by
  apply lratCheckerSound f6354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6354
  · intro a ha; simp [p6354] at ha; subst a; trivial
  · exact checked6354
theorem derived6354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6354 := by
  apply localUnsat_implies_entails f6354 [c2715, c2718, c3420] c6354 unsat6354 (by rfl) a
  have h0 : Entails.eval a c2715 := h 2714 (by decide)
  have h1 : Entails.eval a c2718 := h 2717 (by decide)
  have h2 : Entails.eval a c3420 := h 3419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6355 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6326, some c6227, some c6349, some c5376, some c5381, some c5373, some c5372, some c6322, some c6347, some c5383, some c6350, some c5947, some c3810, some c5371, some c3800, some c5930, some c3808, some c5391, some c5900, some c3940, some c6354, some c3179, some c3159, some c2761, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked6355 : lratChecker f6355 p6355 = .success := by decide +kernel
theorem unsat6355 : Unsatisfiable (PosFin 65) f6355 := by
  apply lratCheckerSound f6355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6355
  · intro a ha; simp [p6355] at ha; subst a; trivial
  · exact checked6355
theorem derived6355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6355 := by
  apply localUnsat_implies_entails f6355 [c6326, c6227, c6349, c5376, c5381, c5373, c5372, c6322, c6347, c5383, c6350, c5947, c3810, c5371, c3800, c5930, c3808, c5391, c5900, c3940, c6354, c3179, c3159, c2761] c6355 unsat6355 (by rfl) a
  have h0 : Entails.eval a c6326 := derived6326 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6349 := derived6349 a h
  have h3 : Entails.eval a c5376 := h 5375 (by decide)
  have h4 : Entails.eval a c5381 := h 5380 (by decide)
  have h5 : Entails.eval a c5373 := h 5372 (by decide)
  have h6 : Entails.eval a c5372 := h 5371 (by decide)
  have h7 : Entails.eval a c6322 := derived6322 a h
  have h8 : Entails.eval a c6347 := derived6347 a h
  have h9 : Entails.eval a c5383 := h 5382 (by decide)
  have h10 : Entails.eval a c6350 := derived6350 a h
  have h11 : Entails.eval a c5947 := derived5947 a h
  have h12 : Entails.eval a c3810 := h 3809 (by decide)
  have h13 : Entails.eval a c5371 := h 5370 (by decide)
  have h14 : Entails.eval a c3800 := h 3799 (by decide)
  have h15 : Entails.eval a c5930 := derived5930 a h
  have h16 : Entails.eval a c3808 := h 3807 (by decide)
  have h17 : Entails.eval a c5391 := h 5390 (by decide)
  have h18 : Entails.eval a c5900 := derived5900 a h
  have h19 : Entails.eval a c3940 := h 3939 (by decide)
  have h20 : Entails.eval a c6354 := derived6354 a h
  have h21 : Entails.eval a c3179 := h 3178 (by decide)
  have h22 : Entails.eval a c3159 := h 3158 (by decide)
  have h23 : Entails.eval a c2761 := h 2760 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6356 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6350, some c6227, some c6349, some c5373, some c5376, some c5381, some c5372, some c5383, some c5371, some c6322, some c6347, some c5947, some c3800, some c3810, some c3808, some c5391, some c6352, some c6326, some c5930, some c5762, some c5900, some c3940, some c5502, some c6355, some c2698, some c2756, some c6353, some c2930, some c3124, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked6356 : lratChecker f6356 p6356 = .success := by decide +kernel
theorem unsat6356 : Unsatisfiable (PosFin 65) f6356 := by
  apply lratCheckerSound f6356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6356
  · intro a ha; simp [p6356] at ha; subst a; trivial
  · exact checked6356
theorem derived6356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6356 := by
  apply localUnsat_implies_entails f6356 [c6350, c6227, c6349, c5373, c5376, c5381, c5372, c5383, c5371, c6322, c6347, c5947, c3800, c3810, c3808, c5391, c6352, c6326, c5930, c5762, c5900, c3940, c5502, c6355, c2698, c2756, c6353, c2930, c3124] c6356 unsat6356 (by rfl) a
  have h0 : Entails.eval a c6350 := derived6350 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6349 := derived6349 a h
  have h3 : Entails.eval a c5373 := h 5372 (by decide)
  have h4 : Entails.eval a c5376 := h 5375 (by decide)
  have h5 : Entails.eval a c5381 := h 5380 (by decide)
  have h6 : Entails.eval a c5372 := h 5371 (by decide)
  have h7 : Entails.eval a c5383 := h 5382 (by decide)
  have h8 : Entails.eval a c5371 := h 5370 (by decide)
  have h9 : Entails.eval a c6322 := derived6322 a h
  have h10 : Entails.eval a c6347 := derived6347 a h
  have h11 : Entails.eval a c5947 := derived5947 a h
  have h12 : Entails.eval a c3800 := h 3799 (by decide)
  have h13 : Entails.eval a c3810 := h 3809 (by decide)
  have h14 : Entails.eval a c3808 := h 3807 (by decide)
  have h15 : Entails.eval a c5391 := h 5390 (by decide)
  have h16 : Entails.eval a c6352 := derived6352 a h
  have h17 : Entails.eval a c6326 := derived6326 a h
  have h18 : Entails.eval a c5930 := derived5930 a h
  have h19 : Entails.eval a c5762 := h 5761 (by decide)
  have h20 : Entails.eval a c5900 := derived5900 a h
  have h21 : Entails.eval a c3940 := h 3939 (by decide)
  have h22 : Entails.eval a c5502 := h 5501 (by decide)
  have h23 : Entails.eval a c6355 := derived6355 a h
  have h24 : Entails.eval a c2698 := h 2697 (by decide)
  have h25 : Entails.eval a c2756 := h 2755 (by decide)
  have h26 : Entails.eval a c6353 := derived6353 a h
  have h27 : Entails.eval a c2930 := h 2929 (by decide)
  have h28 : Entails.eval a c3124 := h 3123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6357 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, false), (⟨35, by decide⟩, false), (⟨58, by decide⟩, true), (⟨44, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2697, some c2757, some c3124, some c2930, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6357 : lratChecker f6357 p6357 = .success := by decide +kernel
theorem unsat6357 : Unsatisfiable (PosFin 65) f6357 := by
  apply lratCheckerSound f6357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6357
  · intro a ha; simp [p6357] at ha; subst a; trivial
  · exact checked6357
theorem derived6357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6357 := by
  apply localUnsat_implies_entails f6357 [c2697, c2757, c3124, c2930] c6357 unsat6357 (by rfl) a
  have h0 : Entails.eval a c2697 := h 2696 (by decide)
  have h1 : Entails.eval a c2757 := h 2756 (by decide)
  have h2 : Entails.eval a c3124 := h 3123 (by decide)
  have h3 : Entails.eval a c2930 := h 2929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6358 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2930, some c2940, some c3262, some c3311, some c3196, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6358 : lratChecker f6358 p6358 = .success := by decide +kernel
theorem unsat6358 : Unsatisfiable (PosFin 65) f6358 := by
  apply lratCheckerSound f6358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6358
  · intro a ha; simp [p6358] at ha; subst a; trivial
  · exact checked6358
theorem derived6358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6358 := by
  apply localUnsat_implies_entails f6358 [c2930, c2940, c3262, c3311, c3196] c6358 unsat6358 (by rfl) a
  have h0 : Entails.eval a c2930 := h 2929 (by decide)
  have h1 : Entails.eval a c2940 := h 2939 (by decide)
  have h2 : Entails.eval a c3262 := h 3261 (by decide)
  have h3 : Entails.eval a c3311 := h 3310 (by decide)
  have h4 : Entails.eval a c3196 := h 3195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6359 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨62, by decide⟩, false), (⟨41, by decide⟩, false), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6358, some c2877, some c2883, some c2963, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6359 : lratChecker f6359 p6359 = .success := by decide +kernel
theorem unsat6359 : Unsatisfiable (PosFin 65) f6359 := by
  apply lratCheckerSound f6359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6359
  · intro a ha; simp [p6359] at ha; subst a; trivial
  · exact checked6359
theorem derived6359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6359 := by
  apply localUnsat_implies_entails f6359 [c6358, c2877, c2883, c2963] c6359 unsat6359 (by rfl) a
  have h0 : Entails.eval a c6358 := derived6358 a h
  have h1 : Entails.eval a c2877 := h 2876 (by decide)
  have h2 : Entails.eval a c2883 := h 2882 (by decide)
  have h3 : Entails.eval a c2963 := h 2962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6360 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨39, by decide⟩, false), (⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨62, by decide⟩, false), (⟨41, by decide⟩, false), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6359, some c2832, some c2838, some c3174, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6360 : lratChecker f6360 p6360 = .success := by decide +kernel
theorem unsat6360 : Unsatisfiable (PosFin 65) f6360 := by
  apply lratCheckerSound f6360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6360
  · intro a ha; simp [p6360] at ha; subst a; trivial
  · exact checked6360
theorem derived6360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6360 := by
  apply localUnsat_implies_entails f6360 [c6359, c2832, c2838, c3174] c6360 unsat6360 (by rfl) a
  have h0 : Entails.eval a c6359 := derived6359 a h
  have h1 : Entails.eval a c2832 := h 2831 (by decide)
  have h2 : Entails.eval a c2838 := h 2837 (by decide)
  have h3 : Entails.eval a c3174 := h 3173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6361 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6350, some c6349, some c6347, some c6326, some c6322, some c6227, some c5373, some c5376, some c5381, some c5372, some c5383, some c5371, some c5930, some c5947, some c3800, some c3810, some c3808, some c5391, some c6352, some c6356, some c5761, some c4633, some c5517, some c6360, some c2697, some c2757, some c6357, some c3037, some c2940, some c2720, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6361 : lratChecker f6361 p6361 = .success := by decide +kernel
theorem unsat6361 : Unsatisfiable (PosFin 65) f6361 := by
  apply lratCheckerSound f6361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6361
  · intro a ha; simp [p6361] at ha; subst a; trivial
  · exact checked6361
theorem derived6361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6361 := by
  apply localUnsat_implies_entails f6361 [c6350, c6349, c6347, c6326, c6322, c6227, c5373, c5376, c5381, c5372, c5383, c5371, c5930, c5947, c3800, c3810, c3808, c5391, c6352, c6356, c5761, c4633, c5517, c6360, c2697, c2757, c6357, c3037, c2940, c2720] c6361 unsat6361 (by rfl) a
  have h0 : Entails.eval a c6350 := derived6350 a h
  have h1 : Entails.eval a c6349 := derived6349 a h
  have h2 : Entails.eval a c6347 := derived6347 a h
  have h3 : Entails.eval a c6326 := derived6326 a h
  have h4 : Entails.eval a c6322 := derived6322 a h
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c5373 := h 5372 (by decide)
  have h7 : Entails.eval a c5376 := h 5375 (by decide)
  have h8 : Entails.eval a c5381 := h 5380 (by decide)
  have h9 : Entails.eval a c5372 := h 5371 (by decide)
  have h10 : Entails.eval a c5383 := h 5382 (by decide)
  have h11 : Entails.eval a c5371 := h 5370 (by decide)
  have h12 : Entails.eval a c5930 := derived5930 a h
  have h13 : Entails.eval a c5947 := derived5947 a h
  have h14 : Entails.eval a c3800 := h 3799 (by decide)
  have h15 : Entails.eval a c3810 := h 3809 (by decide)
  have h16 : Entails.eval a c3808 := h 3807 (by decide)
  have h17 : Entails.eval a c5391 := h 5390 (by decide)
  have h18 : Entails.eval a c6352 := derived6352 a h
  have h19 : Entails.eval a c6356 := derived6356 a h
  have h20 : Entails.eval a c5761 := h 5760 (by decide)
  have h21 : Entails.eval a c4633 := h 4632 (by decide)
  have h22 : Entails.eval a c5517 := h 5516 (by decide)
  have h23 : Entails.eval a c6360 := derived6360 a h
  have h24 : Entails.eval a c2697 := h 2696 (by decide)
  have h25 : Entails.eval a c2757 := h 2756 (by decide)
  have h26 : Entails.eval a c6357 := derived6357 a h
  have h27 : Entails.eval a c3037 := h 3036 (by decide)
  have h28 : Entails.eval a c2940 := h 2939 (by decide)
  have h29 : Entails.eval a c2720 := h 2719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6362 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨35, by decide⟩, false), (⟨58, by decide⟩, true), (⟨44, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, true), (⟨60, by decide⟩, false), (⟨49, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2697, some c2757, some c3037, some c2940, some c2720, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6362 : lratChecker f6362 p6362 = .success := by decide +kernel
theorem unsat6362 : Unsatisfiable (PosFin 65) f6362 := by
  apply lratCheckerSound f6362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6362
  · intro a ha; simp [p6362] at ha; subst a; trivial
  · exact checked6362
theorem derived6362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6362 := by
  apply localUnsat_implies_entails f6362 [c2697, c2757, c3037, c2940, c2720] c6362 unsat6362 (by rfl) a
  have h0 : Entails.eval a c2697 := h 2696 (by decide)
  have h1 : Entails.eval a c2757 := h 2756 (by decide)
  have h2 : Entails.eval a c3037 := h 3036 (by decide)
  have h3 : Entails.eval a c2940 := h 2939 (by decide)
  have h4 : Entails.eval a c2720 := h 2719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6363 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨28, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨41, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨42, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6358, some c2878, some c2884, some c2963, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6363 : lratChecker f6363 p6363 = .success := by decide +kernel
theorem unsat6363 : Unsatisfiable (PosFin 65) f6363 := by
  apply lratCheckerSound f6363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6363
  · intro a ha; simp [p6363] at ha; subst a; trivial
  · exact checked6363
theorem derived6363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6363 := by
  apply localUnsat_implies_entails f6363 [c6358, c2878, c2884, c2963] c6363 unsat6363 (by rfl) a
  have h0 : Entails.eval a c6358 := derived6358 a h
  have h1 : Entails.eval a c2878 := h 2877 (by decide)
  have h2 : Entails.eval a c2884 := h 2883 (by decide)
  have h3 : Entails.eval a c2963 := h 2962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6364 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨37, by decide⟩, true), (⟨55, by decide⟩, false), (⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨41, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨42, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6363, some c2829, some c2835, some c3174, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p6364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6364 : lratChecker f6364 p6364 = .success := by decide +kernel
theorem unsat6364 : Unsatisfiable (PosFin 65) f6364 := by
  apply lratCheckerSound f6364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6364
  · intro a ha; simp [p6364] at ha; subst a; trivial
  · exact checked6364
theorem derived6364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6364 := by
  apply localUnsat_implies_entails f6364 [c6363, c2829, c2835, c3174] c6364 unsat6364 (by rfl) a
  have h0 : Entails.eval a c6363 := derived6363 a h
  have h1 : Entails.eval a c2829 := h 2828 (by decide)
  have h2 : Entails.eval a c2835 := h 2834 (by decide)
  have h3 : Entails.eval a c3174 := h 3173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6365 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, true), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨59, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨42, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true), (⟨47, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4246, some c4249, some c5761, some c4633, some c5517, some c6302, some c6364, some c6357, some c6362, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6365 : lratChecker f6365 p6365 = .success := by decide +kernel
theorem unsat6365 : Unsatisfiable (PosFin 65) f6365 := by
  apply lratCheckerSound f6365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6365
  · intro a ha; simp [p6365] at ha; subst a; trivial
  · exact checked6365
theorem derived6365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6365 := by
  apply localUnsat_implies_entails f6365 [c4246, c4249, c5761, c4633, c5517, c6302, c6364, c6357, c6362] c6365 unsat6365 (by rfl) a
  have h0 : Entails.eval a c4246 := h 4245 (by decide)
  have h1 : Entails.eval a c4249 := h 4248 (by decide)
  have h2 : Entails.eval a c5761 := h 5760 (by decide)
  have h3 : Entails.eval a c4633 := h 4632 (by decide)
  have h4 : Entails.eval a c5517 := h 5516 (by decide)
  have h5 : Entails.eval a c6302 := derived6302 a h
  have h6 : Entails.eval a c6364 := derived6364 a h
  have h7 : Entails.eval a c6357 := derived6357 a h
  have h8 : Entails.eval a c6362 := derived6362 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6366 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6349, some c6347, some c6326, some c6322, some c6227, some c6350, some c6361, some c4158, some c4153, some c5654, some c5656, some c5658, some c4161, some c4246, some c5647, some c5930, some c5947, some c4249, some c5651, some c5666, some c6352, some c6365, some c5900, some c3940, some c6364, some c2698, some c2756, some c2949, some c2930, some c2718, some c3311, some c3124, some c3031, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked6366 : lratChecker f6366 p6366 = .success := by decide +kernel
theorem unsat6366 : Unsatisfiable (PosFin 65) f6366 := by
  apply lratCheckerSound f6366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6366
  · intro a ha; simp [p6366] at ha; subst a; trivial
  · exact checked6366
theorem derived6366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6366 := by
  apply localUnsat_implies_entails f6366 [c6349, c6347, c6326, c6322, c6227, c6350, c6361, c4158, c4153, c5654, c5656, c5658, c4161, c4246, c5647, c5930, c5947, c4249, c5651, c5666, c6352, c6365, c5900, c3940, c6364, c2698, c2756, c2949, c2930, c2718, c3311, c3124, c3031] c6366 unsat6366 (by rfl) a
  have h0 : Entails.eval a c6349 := derived6349 a h
  have h1 : Entails.eval a c6347 := derived6347 a h
  have h2 : Entails.eval a c6326 := derived6326 a h
  have h3 : Entails.eval a c6322 := derived6322 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6350 := derived6350 a h
  have h6 : Entails.eval a c6361 := derived6361 a h
  have h7 : Entails.eval a c4158 := h 4157 (by decide)
  have h8 : Entails.eval a c4153 := h 4152 (by decide)
  have h9 : Entails.eval a c5654 := h 5653 (by decide)
  have h10 : Entails.eval a c5656 := h 5655 (by decide)
  have h11 : Entails.eval a c5658 := h 5657 (by decide)
  have h12 : Entails.eval a c4161 := h 4160 (by decide)
  have h13 : Entails.eval a c4246 := h 4245 (by decide)
  have h14 : Entails.eval a c5647 := h 5646 (by decide)
  have h15 : Entails.eval a c5930 := derived5930 a h
  have h16 : Entails.eval a c5947 := derived5947 a h
  have h17 : Entails.eval a c4249 := h 4248 (by decide)
  have h18 : Entails.eval a c5651 := h 5650 (by decide)
  have h19 : Entails.eval a c5666 := h 5665 (by decide)
  have h20 : Entails.eval a c6352 := derived6352 a h
  have h21 : Entails.eval a c6365 := derived6365 a h
  have h22 : Entails.eval a c5900 := derived5900 a h
  have h23 : Entails.eval a c3940 := h 3939 (by decide)
  have h24 : Entails.eval a c6364 := derived6364 a h
  have h25 : Entails.eval a c2698 := h 2697 (by decide)
  have h26 : Entails.eval a c2756 := h 2755 (by decide)
  have h27 : Entails.eval a c2949 := h 2948 (by decide)
  have h28 : Entails.eval a c2930 := h 2929 (by decide)
  have h29 : Entails.eval a c2718 := h 2717 (by decide)
  have h30 : Entails.eval a c3311 := h 3310 (by decide)
  have h31 : Entails.eval a c3124 := h 3123 (by decide)
  have h32 : Entails.eval a c3031 := h 3030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6367 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6349, some c6326, some c6227, some c4087, some c4084, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6367 : lratChecker f6367 p6367 = .success := by decide +kernel
theorem unsat6367 : Unsatisfiable (PosFin 65) f6367 := by
  apply lratCheckerSound f6367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6367
  · intro a ha; simp [p6367] at ha; subst a; trivial
  · exact checked6367
theorem derived6367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6367 := by
  apply localUnsat_implies_entails f6367 [c6349, c6326, c6227, c4087, c4084] c6367 unsat6367 (by rfl) a
  have h0 : Entails.eval a c6349 := derived6349 a h
  have h1 : Entails.eval a c6326 := derived6326 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c4087 := h 4086 (by decide)
  have h4 : Entails.eval a c4084 := h 4083 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6368 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6349, some c6326, some c6227, some c6367, some c6366, some c4272, some c4269, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6368 : lratChecker f6368 p6368 = .success := by decide +kernel
theorem unsat6368 : Unsatisfiable (PosFin 65) f6368 := by
  apply lratCheckerSound f6368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6368
  · intro a ha; simp [p6368] at ha; subst a; trivial
  · exact checked6368
theorem derived6368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6368 := by
  apply localUnsat_implies_entails f6368 [c6349, c6326, c6227, c6367, c6366, c4272, c4269] c6368 unsat6368 (by rfl) a
  have h0 : Entails.eval a c6349 := derived6349 a h
  have h1 : Entails.eval a c6326 := derived6326 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6367 := derived6367 a h
  have h4 : Entails.eval a c6366 := derived6366 a h
  have h5 : Entails.eval a c4272 := h 4271 (by decide)
  have h6 : Entails.eval a c4269 := h 4268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6369 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3841, some c3569, some c3880, some c4522, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6369 : lratChecker f6369 p6369 = .success := by decide +kernel
theorem unsat6369 : Unsatisfiable (PosFin 65) f6369 := by
  apply lratCheckerSound f6369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6369
  · intro a ha; simp [p6369] at ha; subst a; trivial
  · exact checked6369
theorem derived6369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6369 := by
  apply localUnsat_implies_entails f6369 [c3841, c3569, c3880, c4522] c6369 unsat6369 (by rfl) a
  have h0 : Entails.eval a c3841 := h 3840 (by decide)
  have h1 : Entails.eval a c3569 := h 3568 (by decide)
  have h2 : Entails.eval a c3880 := h 3879 (by decide)
  have h3 : Entails.eval a c4522 := h 4521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6370 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3847, some c3883, some c3575, some c4526, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p6370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6370 : lratChecker f6370 p6370 = .success := by decide +kernel
theorem unsat6370 : Unsatisfiable (PosFin 65) f6370 := by
  apply lratCheckerSound f6370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6370
  · intro a ha; simp [p6370] at ha; subst a; trivial
  · exact checked6370
theorem derived6370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6370 := by
  apply localUnsat_implies_entails f6370 [c3847, c3883, c3575, c4526] c6370 unsat6370 (by rfl) a
  have h0 : Entails.eval a c3847 := h 3846 (by decide)
  have h1 : Entails.eval a c3883 := h 3882 (by decide)
  have h2 : Entails.eval a c3575 := h 3574 (by decide)
  have h3 : Entails.eval a c4526 := h 4525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6371 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6322, some c6349, some c6368, some c6369, some c6370, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6371 : lratChecker f6371 p6371 = .success := by decide +kernel
theorem unsat6371 : Unsatisfiable (PosFin 65) f6371 := by
  apply lratCheckerSound f6371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6371
  · intro a ha; simp [p6371] at ha; subst a; trivial
  · exact checked6371
theorem derived6371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6371 := by
  apply localUnsat_implies_entails f6371 [c6227, c6322, c6349, c6368, c6369, c6370] c6371 unsat6371 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6322 := derived6322 a h
  have h2 : Entails.eval a c6349 := derived6349 a h
  have h3 : Entails.eval a c6368 := derived6368 a h
  have h4 : Entails.eval a c6369 := derived6369 a h
  have h5 : Entails.eval a c6370 := derived6370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6372 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5185, some c5174, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6372 : lratChecker f6372 p6372 = .success := by decide +kernel
theorem unsat6372 : Unsatisfiable (PosFin 65) f6372 := by
  apply lratCheckerSound f6372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6372
  · intro a ha; simp [p6372] at ha; subst a; trivial
  · exact checked6372
theorem derived6372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6372 := by
  apply localUnsat_implies_entails f6372 [c5185, c5174] c6372 unsat6372 (by rfl) a
  have h0 : Entails.eval a c5185 := h 5184 (by decide)
  have h1 : Entails.eval a c5174 := h 5173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6373 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨44, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5213, some c5205, some c5212, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6373 : lratChecker f6373 p6373 = .success := by decide +kernel
theorem unsat6373 : Unsatisfiable (PosFin 65) f6373 := by
  apply lratCheckerSound f6373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6373
  · intro a ha; simp [p6373] at ha; subst a; trivial
  · exact checked6373
theorem derived6373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6373 := by
  apply localUnsat_implies_entails f6373 [c6227, c5213, c5205, c5212] c6373 unsat6373 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5213 := h 5212 (by decide)
  have h2 : Entails.eval a c5205 := h 5204 (by decide)
  have h3 : Entails.eval a c5212 := h 5211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6374 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨62, by decide⟩, false), (⟨37, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6372, some c5870, some c5745, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6374 : lratChecker f6374 p6374 = .success := by decide +kernel
theorem unsat6374 : Unsatisfiable (PosFin 65) f6374 := by
  apply lratCheckerSound f6374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6374
  · intro a ha; simp [p6374] at ha; subst a; trivial
  · exact checked6374
theorem derived6374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6374 := by
  apply localUnsat_implies_entails f6374 [c6372, c5870, c5745] c6374 unsat6374 (by rfl) a
  have h0 : Entails.eval a c6372 := derived6372 a h
  have h1 : Entails.eval a c5870 := h 5869 (by decide)
  have h2 : Entails.eval a c5745 := h 5744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6375 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6374, some c5862, some c5900, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p6375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6375 : lratChecker f6375 p6375 = .success := by decide +kernel
theorem unsat6375 : Unsatisfiable (PosFin 65) f6375 := by
  apply lratCheckerSound f6375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6375
  · intro a ha; simp [p6375] at ha; subst a; trivial
  · exact checked6375
theorem derived6375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6375 := by
  apply localUnsat_implies_entails f6375 [c6374, c5862, c5900] c6375 unsat6375 (by rfl) a
  have h0 : Entails.eval a c6374 := derived6374 a h
  have h1 : Entails.eval a c5862 := h 5861 (by decide)
  have h2 : Entails.eval a c5900 := derived5900 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6376 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨37, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6372, some c5870, some c5858, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6376 : lratChecker f6376 p6376 = .success := by decide +kernel
theorem unsat6376 : Unsatisfiable (PosFin 65) f6376 := by
  apply lratCheckerSound f6376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6376
  · intro a ha; simp [p6376] at ha; subst a; trivial
  · exact checked6376
theorem derived6376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6376 := by
  apply localUnsat_implies_entails f6376 [c6372, c5870, c5858] c6376 unsat6376 (by rfl) a
  have h0 : Entails.eval a c6372 := derived6372 a h
  have h1 : Entails.eval a c5870 := h 5869 (by decide)
  have h2 : Entails.eval a c5858 := h 5857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6377 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4516, some c6373, some c6375, some c4519, some c6376, some c5862, some c5555, some c5021, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6377 : lratChecker f6377 p6377 = .success := by decide +kernel
theorem unsat6377 : Unsatisfiable (PosFin 65) f6377 := by
  apply lratCheckerSound f6377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6377
  · intro a ha; simp [p6377] at ha; subst a; trivial
  · exact checked6377
theorem derived6377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6377 := by
  apply localUnsat_implies_entails f6377 [c6227, c4516, c6373, c6375, c4519, c6376, c5862, c5555, c5021] c6377 unsat6377 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4516 := h 4515 (by decide)
  have h2 : Entails.eval a c6373 := derived6373 a h
  have h3 : Entails.eval a c6375 := derived6375 a h
  have h4 : Entails.eval a c4519 := h 4518 (by decide)
  have h5 : Entails.eval a c6376 := derived6376 a h
  have h6 : Entails.eval a c5862 := h 5861 (by decide)
  have h7 : Entails.eval a c5555 := h 5554 (by decide)
  have h8 : Entails.eval a c5021 := h 5020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6378 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨37, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5052, some c5177, some c5629, some c5734, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6378 : lratChecker f6378 p6378 = .success := by decide +kernel
theorem unsat6378 : Unsatisfiable (PosFin 65) f6378 := by
  apply lratCheckerSound f6378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6378
  · intro a ha; simp [p6378] at ha; subst a; trivial
  · exact checked6378
theorem derived6378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6378 := by
  apply localUnsat_implies_entails f6378 [c5052, c5177, c5629, c5734] c6378 unsat6378 (by rfl) a
  have h0 : Entails.eval a c5052 := h 5051 (by decide)
  have h1 : Entails.eval a c5177 := h 5176 (by decide)
  have h2 : Entails.eval a c5629 := h 5628 (by decide)
  have h3 : Entails.eval a c5734 := h 5733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6379 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨58, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5742, some c5734, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6379 : lratChecker f6379 p6379 = .success := by decide +kernel
theorem unsat6379 : Unsatisfiable (PosFin 65) f6379 := by
  apply lratCheckerSound f6379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6379
  · intro a ha; simp [p6379] at ha; subst a; trivial
  · exact checked6379
theorem derived6379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6379 := by
  apply localUnsat_implies_entails f6379 [c5742, c5734] c6379 unsat6379 (by rfl) a
  have h0 : Entails.eval a c5742 := h 5741 (by decide)
  have h1 : Entails.eval a c5734 := h 5733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6380 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6379, some c6378, some c6372, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6380 : lratChecker f6380 p6380 = .success := by decide +kernel
theorem unsat6380 : Unsatisfiable (PosFin 65) f6380 := by
  apply lratCheckerSound f6380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6380
  · intro a ha; simp [p6380] at ha; subst a; trivial
  · exact checked6380
theorem derived6380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6380 := by
  apply localUnsat_implies_entails f6380 [c6379, c6378, c6372] c6380 unsat6380 (by rfl) a
  have h0 : Entails.eval a c6379 := derived6379 a h
  have h1 : Entails.eval a c6378 := derived6378 a h
  have h2 : Entails.eval a c6372 := derived6372 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived6380

end CochromaticTwenty.Certificates.FixedCore1
