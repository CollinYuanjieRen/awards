import MerLeanExperiment.Certificates.FixedCore0.Steps0700_0799

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8351 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨40, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c8343, some c8328, some c8345, some c7716, some c8269, some c8339, some c6789, some c6927, some c8347, some c7104, some c7454, some c6587, some c7994, some c8346, some c8333, some c6291, some c6913, some c7140, some c6762, some c3865, some c3937, some c531, some c55, some c4654, some c2907, some c4330, some c98, some c3762, some c5570, some c112, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked8351 : lratChecker f8351 p8351 = .success := by decide +kernel
theorem unsat8351 : Unsatisfiable (PosFin 65) f8351 := by
  apply lratCheckerSound f8351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8351
  · intro a ha; simp [p8351] at ha; subst a; trivial
  · exact checked8351
theorem derived8351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8351 := by
  apply localUnsat_implies_entails f8351 [c8300, c8343, c8328, c8345, c7716, c8269, c8339, c6789, c6927, c8347, c7104, c7454, c6587, c7994, c8346, c8333, c6291, c6913, c7140, c6762, c3865, c3937, c531, c55, c4654, c2907, c4330, c98, c3762, c5570, c112] c8351 unsat8351 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c8343 := derived8343 a h
  have h2 : Entails.eval a c8328 := derived8328 a h
  have h3 : Entails.eval a c8345 := derived8345 a h
  have h4 : Entails.eval a c7716 := derived7716 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c8339 := derived8339 a h
  have h7 : Entails.eval a c6789 := h 6788 (by decide)
  have h8 : Entails.eval a c6927 := h 6926 (by decide)
  have h9 : Entails.eval a c8347 := derived8347 a h
  have h10 : Entails.eval a c7104 := h 7103 (by decide)
  have h11 : Entails.eval a c7454 := h 7453 (by decide)
  have h12 : Entails.eval a c6587 := h 6586 (by decide)
  have h13 : Entails.eval a c7994 := derived7994 a h
  have h14 : Entails.eval a c8346 := derived8346 a h
  have h15 : Entails.eval a c8333 := derived8333 a h
  have h16 : Entails.eval a c6291 := h 6290 (by decide)
  have h17 : Entails.eval a c6913 := h 6912 (by decide)
  have h18 : Entails.eval a c7140 := h 7139 (by decide)
  have h19 : Entails.eval a c6762 := h 6761 (by decide)
  have h20 : Entails.eval a c3865 := h 3864 (by decide)
  have h21 : Entails.eval a c3937 := h 3936 (by decide)
  have h22 : Entails.eval a c531 := h 530 (by decide)
  have h23 : Entails.eval a c55 := h 54 (by decide)
  have h24 : Entails.eval a c4654 := h 4653 (by decide)
  have h25 : Entails.eval a c2907 := h 2906 (by decide)
  have h26 : Entails.eval a c4330 := h 4329 (by decide)
  have h27 : Entails.eval a c98 := h 97 (by decide)
  have h28 : Entails.eval a c3762 := h 3761 (by decide)
  have h29 : Entails.eval a c5570 := h 5569 (by decide)
  have h30 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8352 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8343, some c7994, some c8300, some c8328, some c6913, some c7140, some c8339, some c8345, some c8347, some c6836, some c6587, some c6927, some c6789, some c8346, some c8333, some c6291, some c6410, some c6413, some c6881, some c7716, some c8269, some c7104, some c7454, some c6762, some c8350, some c8351, some c8348, some c4330, some c4286, some c4174, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked8352 : lratChecker f8352 p8352 = .success := by decide +kernel
theorem unsat8352 : Unsatisfiable (PosFin 65) f8352 := by
  apply lratCheckerSound f8352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8352
  · intro a ha; simp [p8352] at ha; subst a; trivial
  · exact checked8352
theorem derived8352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8352 := by
  apply localUnsat_implies_entails f8352 [c8343, c7994, c8300, c8328, c6913, c7140, c8339, c8345, c8347, c6836, c6587, c6927, c6789, c8346, c8333, c6291, c6410, c6413, c6881, c7716, c8269, c7104, c7454, c6762, c8350, c8351, c8348, c4330, c4286, c4174] c8352 unsat8352 (by rfl) a
  have h0 : Entails.eval a c8343 := derived8343 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c8300 := derived8300 a h
  have h3 : Entails.eval a c8328 := derived8328 a h
  have h4 : Entails.eval a c6913 := h 6912 (by decide)
  have h5 : Entails.eval a c7140 := h 7139 (by decide)
  have h6 : Entails.eval a c8339 := derived8339 a h
  have h7 : Entails.eval a c8345 := derived8345 a h
  have h8 : Entails.eval a c8347 := derived8347 a h
  have h9 : Entails.eval a c6836 := h 6835 (by decide)
  have h10 : Entails.eval a c6587 := h 6586 (by decide)
  have h11 : Entails.eval a c6927 := h 6926 (by decide)
  have h12 : Entails.eval a c6789 := h 6788 (by decide)
  have h13 : Entails.eval a c8346 := derived8346 a h
  have h14 : Entails.eval a c8333 := derived8333 a h
  have h15 : Entails.eval a c6291 := h 6290 (by decide)
  have h16 : Entails.eval a c6410 := h 6409 (by decide)
  have h17 : Entails.eval a c6413 := h 6412 (by decide)
  have h18 : Entails.eval a c6881 := h 6880 (by decide)
  have h19 : Entails.eval a c7716 := derived7716 a h
  have h20 : Entails.eval a c8269 := derived8269 a h
  have h21 : Entails.eval a c7104 := h 7103 (by decide)
  have h22 : Entails.eval a c7454 := h 7453 (by decide)
  have h23 : Entails.eval a c6762 := h 6761 (by decide)
  have h24 : Entails.eval a c8350 := derived8350 a h
  have h25 : Entails.eval a c8351 := derived8351 a h
  have h26 : Entails.eval a c8348 := derived8348 a h
  have h27 : Entails.eval a c4330 := h 4329 (by decide)
  have h28 : Entails.eval a c4286 := h 4285 (by decide)
  have h29 : Entails.eval a c4174 := h 4173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8353 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨42, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4330, some c4286, some c4174, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8353 : lratChecker f8353 p8353 = .success := by decide +kernel
theorem unsat8353 : Unsatisfiable (PosFin 65) f8353 := by
  apply lratCheckerSound f8353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8353
  · intro a ha; simp [p8353] at ha; subst a; trivial
  · exact checked8353
theorem derived8353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8353 := by
  apply localUnsat_implies_entails f8353 [c4330, c4286, c4174] c8353 unsat8353 (by rfl) a
  have h0 : Entails.eval a c4330 := h 4329 (by decide)
  have h1 : Entails.eval a c4286 := h 4285 (by decide)
  have h2 : Entails.eval a c4174 := h 4173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8354 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1494, some c3975, some c2568, some c1141, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p8354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8354 : lratChecker f8354 p8354 = .success := by decide +kernel
theorem unsat8354 : Unsatisfiable (PosFin 65) f8354 := by
  apply lratCheckerSound f8354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8354
  · intro a ha; simp [p8354] at ha; subst a; trivial
  · exact checked8354
theorem derived8354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8354 := by
  apply localUnsat_implies_entails f8354 [c1494, c3975, c2568, c1141] c8354 unsat8354 (by rfl) a
  have h0 : Entails.eval a c1494 := h 1493 (by decide)
  have h1 : Entails.eval a c3975 := h 3974 (by decide)
  have h2 : Entails.eval a c2568 := h 2567 (by decide)
  have h3 : Entails.eval a c1141 := h 1140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8355 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨58, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, true), (⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨60, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, true), (⟨35, by decide⟩, true), (⟨59, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8354, some c8353, some c3137, some c2943, some c3611, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p8355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8355 : lratChecker f8355 p8355 = .success := by decide +kernel
theorem unsat8355 : Unsatisfiable (PosFin 65) f8355 := by
  apply lratCheckerSound f8355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8355
  · intro a ha; simp [p8355] at ha; subst a; trivial
  · exact checked8355
theorem derived8355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8355 := by
  apply localUnsat_implies_entails f8355 [c8354, c8353, c3137, c2943, c3611] c8355 unsat8355 (by rfl) a
  have h0 : Entails.eval a c8354 := derived8354 a h
  have h1 : Entails.eval a c8353 := derived8353 a h
  have h2 : Entails.eval a c3137 := h 3136 (by decide)
  have h3 : Entails.eval a c2943 := h 2942 (by decide)
  have h4 : Entails.eval a c3611 := h 3610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8356 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c8343, some c6789, some c8339, some c6927, some c8328, some c8345, some c8347, some c7104, some c6587, some c7994, some c8346, some c8333, some c6291, some c6913, some c7140, some c6762, some c7716, some c8269, some c6836, some c6410, some c7454, some c8352, some c8355, some c531, some c530, some c8351, some c3538, some c4475, some c3446, some c3821, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked8356 : lratChecker f8356 p8356 = .success := by decide +kernel
theorem unsat8356 : Unsatisfiable (PosFin 65) f8356 := by
  apply lratCheckerSound f8356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8356
  · intro a ha; simp [p8356] at ha; subst a; trivial
  · exact checked8356
theorem derived8356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8356 := by
  apply localUnsat_implies_entails f8356 [c8300, c8343, c6789, c8339, c6927, c8328, c8345, c8347, c7104, c6587, c7994, c8346, c8333, c6291, c6913, c7140, c6762, c7716, c8269, c6836, c6410, c7454, c8352, c8355, c531, c530, c8351, c3538, c4475, c3446, c3821] c8356 unsat8356 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c8343 := derived8343 a h
  have h2 : Entails.eval a c6789 := h 6788 (by decide)
  have h3 : Entails.eval a c8339 := derived8339 a h
  have h4 : Entails.eval a c6927 := h 6926 (by decide)
  have h5 : Entails.eval a c8328 := derived8328 a h
  have h6 : Entails.eval a c8345 := derived8345 a h
  have h7 : Entails.eval a c8347 := derived8347 a h
  have h8 : Entails.eval a c7104 := h 7103 (by decide)
  have h9 : Entails.eval a c6587 := h 6586 (by decide)
  have h10 : Entails.eval a c7994 := derived7994 a h
  have h11 : Entails.eval a c8346 := derived8346 a h
  have h12 : Entails.eval a c8333 := derived8333 a h
  have h13 : Entails.eval a c6291 := h 6290 (by decide)
  have h14 : Entails.eval a c6913 := h 6912 (by decide)
  have h15 : Entails.eval a c7140 := h 7139 (by decide)
  have h16 : Entails.eval a c6762 := h 6761 (by decide)
  have h17 : Entails.eval a c7716 := derived7716 a h
  have h18 : Entails.eval a c8269 := derived8269 a h
  have h19 : Entails.eval a c6836 := h 6835 (by decide)
  have h20 : Entails.eval a c6410 := h 6409 (by decide)
  have h21 : Entails.eval a c7454 := h 7453 (by decide)
  have h22 : Entails.eval a c8352 := derived8352 a h
  have h23 : Entails.eval a c8355 := derived8355 a h
  have h24 : Entails.eval a c531 := h 530 (by decide)
  have h25 : Entails.eval a c530 := h 529 (by decide)
  have h26 : Entails.eval a c8351 := derived8351 a h
  have h27 : Entails.eval a c3538 := h 3537 (by decide)
  have h28 : Entails.eval a c4475 := h 4474 (by decide)
  have h29 : Entails.eval a c3446 := h 3445 (by decide)
  have h30 : Entails.eval a c3821 := h 3820 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8357 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨61, by decide⟩, false), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨60, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7158, some c8300, some c7994, some c531, some c530, some c55, some c2232, some c2909, some c1088, some c1140, some c97, some c3717, some c5569, some c113, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8357 : lratChecker f8357 p8357 = .success := by decide +kernel
theorem unsat8357 : Unsatisfiable (PosFin 65) f8357 := by
  apply lratCheckerSound f8357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8357
  · intro a ha; simp [p8357] at ha; subst a; trivial
  · exact checked8357
theorem derived8357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8357 := by
  apply localUnsat_implies_entails f8357 [c8269, c7158, c8300, c7994, c531, c530, c55, c2232, c2909, c1088, c1140, c97, c3717, c5569, c113] c8357 unsat8357 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7158 := h 7157 (by decide)
  have h2 : Entails.eval a c8300 := derived8300 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c531 := h 530 (by decide)
  have h5 : Entails.eval a c530 := h 529 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c2232 := h 2231 (by decide)
  have h8 : Entails.eval a c2909 := h 2908 (by decide)
  have h9 : Entails.eval a c1088 := h 1087 (by decide)
  have h10 : Entails.eval a c1140 := h 1139 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c3717 := h 3716 (by decide)
  have h13 : Entails.eval a c5569 := h 5568 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8358 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c510, some c947, some c1663, some c4261, some c3447, some c1264, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8358 : lratChecker f8358 p8358 = .success := by decide +kernel
theorem unsat8358 : Unsatisfiable (PosFin 65) f8358 := by
  apply lratCheckerSound f8358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8358
  · intro a ha; simp [p8358] at ha; subst a; trivial
  · exact checked8358
theorem derived8358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8358 := by
  apply localUnsat_implies_entails f8358 [c8300, c510, c947, c1663, c4261, c3447, c1264] c8358 unsat8358 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c510 := h 509 (by decide)
  have h2 : Entails.eval a c947 := h 946 (by decide)
  have h3 : Entails.eval a c1663 := h 1662 (by decide)
  have h4 : Entails.eval a c4261 := h 4260 (by decide)
  have h5 : Entails.eval a c3447 := h 3446 (by decide)
  have h6 : Entails.eval a c1264 := h 1263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8359 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8328, some c8339, some c8345, some c8347, some c8300, some c8343, some c7716, some c8269, some c7994, some c6587, some c6927, some c6913, some c6789, some c8346, some c8333, some c8356, some c7158, some c6684, some c7039, some c8357, some c8358, some c3472, some c3498, some c2526, some c2895, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked8359 : lratChecker f8359 p8359 = .success := by decide +kernel
theorem unsat8359 : Unsatisfiable (PosFin 65) f8359 := by
  apply lratCheckerSound f8359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8359
  · intro a ha; simp [p8359] at ha; subst a; trivial
  · exact checked8359
theorem derived8359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8359 := by
  apply localUnsat_implies_entails f8359 [c8328, c8339, c8345, c8347, c8300, c8343, c7716, c8269, c7994, c6587, c6927, c6913, c6789, c8346, c8333, c8356, c7158, c6684, c7039, c8357, c8358, c3472, c3498, c2526, c2895] c8359 unsat8359 (by rfl) a
  have h0 : Entails.eval a c8328 := derived8328 a h
  have h1 : Entails.eval a c8339 := derived8339 a h
  have h2 : Entails.eval a c8345 := derived8345 a h
  have h3 : Entails.eval a c8347 := derived8347 a h
  have h4 : Entails.eval a c8300 := derived8300 a h
  have h5 : Entails.eval a c8343 := derived8343 a h
  have h6 : Entails.eval a c7716 := derived7716 a h
  have h7 : Entails.eval a c8269 := derived8269 a h
  have h8 : Entails.eval a c7994 := derived7994 a h
  have h9 : Entails.eval a c6587 := h 6586 (by decide)
  have h10 : Entails.eval a c6927 := h 6926 (by decide)
  have h11 : Entails.eval a c6913 := h 6912 (by decide)
  have h12 : Entails.eval a c6789 := h 6788 (by decide)
  have h13 : Entails.eval a c8346 := derived8346 a h
  have h14 : Entails.eval a c8333 := derived8333 a h
  have h15 : Entails.eval a c8356 := derived8356 a h
  have h16 : Entails.eval a c7158 := h 7157 (by decide)
  have h17 : Entails.eval a c6684 := h 6683 (by decide)
  have h18 : Entails.eval a c7039 := h 7038 (by decide)
  have h19 : Entails.eval a c8357 := derived8357 a h
  have h20 : Entails.eval a c8358 := derived8358 a h
  have h21 : Entails.eval a c3472 := h 3471 (by decide)
  have h22 : Entails.eval a c3498 := h 3497 (by decide)
  have h23 : Entails.eval a c2526 := h 2525 (by decide)
  have h24 : Entails.eval a c2895 := h 2894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8360 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨62, by decide⟩, false), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c3472, some c3498, some c2526, some c2895, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8360 : lratChecker f8360 p8360 = .success := by decide +kernel
theorem unsat8360 : Unsatisfiable (PosFin 65) f8360 := by
  apply lratCheckerSound f8360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8360
  · intro a ha; simp [p8360] at ha; subst a; trivial
  · exact checked8360
theorem derived8360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8360 := by
  apply localUnsat_implies_entails f8360 [c8269, c3472, c3498, c2526, c2895] c8360 unsat8360 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c3472 := h 3471 (by decide)
  have h2 : Entails.eval a c3498 := h 3497 (by decide)
  have h3 : Entails.eval a c2526 := h 2525 (by decide)
  have h4 : Entails.eval a c2895 := h 2894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8361 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8360, some c947, some c946, some c1637, some c3445, some c4250, some c1288, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8361 : lratChecker f8361 p8361 = .success := by decide +kernel
theorem unsat8361 : Unsatisfiable (PosFin 65) f8361 := by
  apply lratCheckerSound f8361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8361
  · intro a ha; simp [p8361] at ha; subst a; trivial
  · exact checked8361
theorem derived8361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8361 := by
  apply localUnsat_implies_entails f8361 [c8269, c8360, c947, c946, c1637, c3445, c4250, c1288] c8361 unsat8361 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8360 := derived8360 a h
  have h2 : Entails.eval a c947 := h 946 (by decide)
  have h3 : Entails.eval a c946 := h 945 (by decide)
  have h4 : Entails.eval a c1637 := h 1636 (by decide)
  have h5 : Entails.eval a c3445 := h 3444 (by decide)
  have h6 : Entails.eval a c4250 := h 4249 (by decide)
  have h7 : Entails.eval a c1288 := h 1287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8362 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, false), (⟨57, by decide⟩, true), (⟨60, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨37, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7243, some c7137, some c7308, some c7994, some c7158, some c6684, some c6693, some c7039, some c8361, some c532, some c529, some c57, some c2231, some c2909, some c1136, some c1084, some c97, some c4607, some c3714, some c5600, some c5569, some c293, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8362 : lratChecker f8362 p8362 = .success := by decide +kernel
theorem unsat8362 : Unsatisfiable (PosFin 65) f8362 := by
  apply lratCheckerSound f8362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8362
  · intro a ha; simp [p8362] at ha; subst a; trivial
  · exact checked8362
theorem derived8362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8362 := by
  apply localUnsat_implies_entails f8362 [c8269, c7243, c7137, c7308, c7994, c7158, c6684, c6693, c7039, c8361, c532, c529, c57, c2231, c2909, c1136, c1084, c97, c4607, c3714, c5600, c5569, c293] c8362 unsat8362 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7243 := h 7242 (by decide)
  have h2 : Entails.eval a c7137 := h 7136 (by decide)
  have h3 : Entails.eval a c7308 := h 7307 (by decide)
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c7158 := h 7157 (by decide)
  have h6 : Entails.eval a c6684 := h 6683 (by decide)
  have h7 : Entails.eval a c6693 := h 6692 (by decide)
  have h8 : Entails.eval a c7039 := h 7038 (by decide)
  have h9 : Entails.eval a c8361 := derived8361 a h
  have h10 : Entails.eval a c532 := h 531 (by decide)
  have h11 : Entails.eval a c529 := h 528 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c2231 := h 2230 (by decide)
  have h14 : Entails.eval a c2909 := h 2908 (by decide)
  have h15 : Entails.eval a c1136 := h 1135 (by decide)
  have h16 : Entails.eval a c1084 := h 1083 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c4607 := h 4606 (by decide)
  have h19 : Entails.eval a c3714 := h 3713 (by decide)
  have h20 : Entails.eval a c5600 := h 5599 (by decide)
  have h21 : Entails.eval a c5569 := h 5568 (by decide)
  have h22 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8363 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c8328, some c8345, some c8300, some c8343, some c7716, some c8339, some c8347, some c8359, some c6581, some c6910, some c8269, some c6783, some c6922, some c8362, some c7137, some c7243, some c7454, some c7283, some c6836, some c7308, some c6288, some c6410, some c6413, some c6741, some c532, some c529, some c57, some c2239, some c2906, some c1138, some c1084, some c98, some c4610, some c3713, some c5601, some c5570, some c293, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked8363 : lratChecker f8363 p8363 = .success := by decide +kernel
theorem unsat8363 : Unsatisfiable (PosFin 65) f8363 := by
  apply lratCheckerSound f8363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8363
  · intro a ha; simp [p8363] at ha; subst a; trivial
  · exact checked8363
theorem derived8363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8363 := by
  apply localUnsat_implies_entails f8363 [c7994, c8328, c8345, c8300, c8343, c7716, c8339, c8347, c8359, c6581, c6910, c8269, c6783, c6922, c8362, c7137, c7243, c7454, c7283, c6836, c7308, c6288, c6410, c6413, c6741, c532, c529, c57, c2239, c2906, c1138, c1084, c98, c4610, c3713, c5601, c5570, c293] c8363 unsat8363 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c8328 := derived8328 a h
  have h2 : Entails.eval a c8345 := derived8345 a h
  have h3 : Entails.eval a c8300 := derived8300 a h
  have h4 : Entails.eval a c8343 := derived8343 a h
  have h5 : Entails.eval a c7716 := derived7716 a h
  have h6 : Entails.eval a c8339 := derived8339 a h
  have h7 : Entails.eval a c8347 := derived8347 a h
  have h8 : Entails.eval a c8359 := derived8359 a h
  have h9 : Entails.eval a c6581 := h 6580 (by decide)
  have h10 : Entails.eval a c6910 := h 6909 (by decide)
  have h11 : Entails.eval a c8269 := derived8269 a h
  have h12 : Entails.eval a c6783 := h 6782 (by decide)
  have h13 : Entails.eval a c6922 := h 6921 (by decide)
  have h14 : Entails.eval a c8362 := derived8362 a h
  have h15 : Entails.eval a c7137 := h 7136 (by decide)
  have h16 : Entails.eval a c7243 := h 7242 (by decide)
  have h17 : Entails.eval a c7454 := h 7453 (by decide)
  have h18 : Entails.eval a c7283 := h 7282 (by decide)
  have h19 : Entails.eval a c6836 := h 6835 (by decide)
  have h20 : Entails.eval a c7308 := h 7307 (by decide)
  have h21 : Entails.eval a c6288 := h 6287 (by decide)
  have h22 : Entails.eval a c6410 := h 6409 (by decide)
  have h23 : Entails.eval a c6413 := h 6412 (by decide)
  have h24 : Entails.eval a c6741 := h 6740 (by decide)
  have h25 : Entails.eval a c532 := h 531 (by decide)
  have h26 : Entails.eval a c529 := h 528 (by decide)
  have h27 : Entails.eval a c57 := h 56 (by decide)
  have h28 : Entails.eval a c2239 := h 2238 (by decide)
  have h29 : Entails.eval a c2906 := h 2905 (by decide)
  have h30 : Entails.eval a c1138 := h 1137 (by decide)
  have h31 : Entails.eval a c1084 := h 1083 (by decide)
  have h32 : Entails.eval a c98 := h 97 (by decide)
  have h33 : Entails.eval a c4610 := h 4609 (by decide)
  have h34 : Entails.eval a c3713 := h 3712 (by decide)
  have h35 : Entails.eval a c5601 := h 5600 (by decide)
  have h36 : Entails.eval a c5570 := h 5569 (by decide)
  have h37 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8364 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8343, some c8339, some c8359, some c6581, some c8300, some c8328, some c8345, some c7716, some c8269, some c6910, some c7243, some c7137, some c7308, some c6741, some c6783, some c6922, some c7008, some c6288, some c8347, some c8362, some c8363, some c8354, some c948, some c3588, some c4223, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked8364 : lratChecker f8364 p8364 = .success := by decide +kernel
theorem unsat8364 : Unsatisfiable (PosFin 65) f8364 := by
  apply lratCheckerSound f8364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8364
  · intro a ha; simp [p8364] at ha; subst a; trivial
  · exact checked8364
theorem derived8364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8364 := by
  apply localUnsat_implies_entails f8364 [c8343, c8339, c8359, c6581, c8300, c8328, c8345, c7716, c8269, c6910, c7243, c7137, c7308, c6741, c6783, c6922, c7008, c6288, c8347, c8362, c8363, c8354, c948, c3588, c4223] c8364 unsat8364 (by rfl) a
  have h0 : Entails.eval a c8343 := derived8343 a h
  have h1 : Entails.eval a c8339 := derived8339 a h
  have h2 : Entails.eval a c8359 := derived8359 a h
  have h3 : Entails.eval a c6581 := h 6580 (by decide)
  have h4 : Entails.eval a c8300 := derived8300 a h
  have h5 : Entails.eval a c8328 := derived8328 a h
  have h6 : Entails.eval a c8345 := derived8345 a h
  have h7 : Entails.eval a c7716 := derived7716 a h
  have h8 : Entails.eval a c8269 := derived8269 a h
  have h9 : Entails.eval a c6910 := h 6909 (by decide)
  have h10 : Entails.eval a c7243 := h 7242 (by decide)
  have h11 : Entails.eval a c7137 := h 7136 (by decide)
  have h12 : Entails.eval a c7308 := h 7307 (by decide)
  have h13 : Entails.eval a c6741 := h 6740 (by decide)
  have h14 : Entails.eval a c6783 := h 6782 (by decide)
  have h15 : Entails.eval a c6922 := h 6921 (by decide)
  have h16 : Entails.eval a c7008 := h 7007 (by decide)
  have h17 : Entails.eval a c6288 := h 6287 (by decide)
  have h18 : Entails.eval a c8347 := derived8347 a h
  have h19 : Entails.eval a c8362 := derived8362 a h
  have h20 : Entails.eval a c8363 := derived8363 a h
  have h21 : Entails.eval a c8354 := derived8354 a h
  have h22 : Entails.eval a c948 := h 947 (by decide)
  have h23 : Entails.eval a c3588 := h 3587 (by decide)
  have h24 : Entails.eval a c4223 := h 4222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8365 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8343, some c8339, some c8328, some c8300, some c8269, some c8345, some c7716, some c8347, some c8359, some c6581, some c6910, some c6783, some c6922, some c7243, some c7137, some c7008, some c7308, some c6741, some c6288, some c8362, some c8363, some c8354, some c8353, some c8364, some c3472, some c3540, some c2943, some c3416, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked8365 : lratChecker f8365 p8365 = .success := by decide +kernel
theorem unsat8365 : Unsatisfiable (PosFin 65) f8365 := by
  apply lratCheckerSound f8365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8365
  · intro a ha; simp [p8365] at ha; subst a; trivial
  · exact checked8365
theorem derived8365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8365 := by
  apply localUnsat_implies_entails f8365 [c8343, c8339, c8328, c8300, c8269, c8345, c7716, c8347, c8359, c6581, c6910, c6783, c6922, c7243, c7137, c7008, c7308, c6741, c6288, c8362, c8363, c8354, c8353, c8364, c3472, c3540, c2943, c3416] c8365 unsat8365 (by rfl) a
  have h0 : Entails.eval a c8343 := derived8343 a h
  have h1 : Entails.eval a c8339 := derived8339 a h
  have h2 : Entails.eval a c8328 := derived8328 a h
  have h3 : Entails.eval a c8300 := derived8300 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c8345 := derived8345 a h
  have h6 : Entails.eval a c7716 := derived7716 a h
  have h7 : Entails.eval a c8347 := derived8347 a h
  have h8 : Entails.eval a c8359 := derived8359 a h
  have h9 : Entails.eval a c6581 := h 6580 (by decide)
  have h10 : Entails.eval a c6910 := h 6909 (by decide)
  have h11 : Entails.eval a c6783 := h 6782 (by decide)
  have h12 : Entails.eval a c6922 := h 6921 (by decide)
  have h13 : Entails.eval a c7243 := h 7242 (by decide)
  have h14 : Entails.eval a c7137 := h 7136 (by decide)
  have h15 : Entails.eval a c7008 := h 7007 (by decide)
  have h16 : Entails.eval a c7308 := h 7307 (by decide)
  have h17 : Entails.eval a c6741 := h 6740 (by decide)
  have h18 : Entails.eval a c6288 := h 6287 (by decide)
  have h19 : Entails.eval a c8362 := derived8362 a h
  have h20 : Entails.eval a c8363 := derived8363 a h
  have h21 : Entails.eval a c8354 := derived8354 a h
  have h22 : Entails.eval a c8353 := derived8353 a h
  have h23 : Entails.eval a c8364 := derived8364 a h
  have h24 : Entails.eval a c3472 := h 3471 (by decide)
  have h25 : Entails.eval a c3540 := h 3539 (by decide)
  have h26 : Entails.eval a c2943 := h 2942 (by decide)
  have h27 : Entails.eval a c3416 := h 3415 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8366 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8328, some c8339, some c8343, some c8365, some c6895, some c7165, some c6909, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8366 : lratChecker f8366 p8366 = .success := by decide +kernel
theorem unsat8366 : Unsatisfiable (PosFin 65) f8366 := by
  apply lratCheckerSound f8366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8366
  · intro a ha; simp [p8366] at ha; subst a; trivial
  · exact checked8366
theorem derived8366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8366 := by
  apply localUnsat_implies_entails f8366 [c8328, c8339, c8343, c8365, c6895, c7165, c6909] c8366 unsat8366 (by rfl) a
  have h0 : Entails.eval a c8328 := derived8328 a h
  have h1 : Entails.eval a c8339 := derived8339 a h
  have h2 : Entails.eval a c8343 := derived8343 a h
  have h3 : Entails.eval a c8365 := derived8365 a h
  have h4 : Entails.eval a c6895 := h 6894 (by decide)
  have h5 : Entails.eval a c7165 := h 7164 (by decide)
  have h6 : Entails.eval a c6909 := h 6908 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8367 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c3471, some c3496, some c2902, some c3438, some c5123, some c2512, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8367 : lratChecker f8367 p8367 = .success := by decide +kernel
theorem unsat8367 : Unsatisfiable (PosFin 65) f8367 := by
  apply lratCheckerSound f8367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8367
  · intro a ha; simp [p8367] at ha; subst a; trivial
  · exact checked8367
theorem derived8367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8367 := by
  apply localUnsat_implies_entails f8367 [c8269, c3471, c3496, c2902, c3438, c5123, c2512] c8367 unsat8367 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c3471 := h 3470 (by decide)
  have h2 : Entails.eval a c3496 := h 3495 (by decide)
  have h3 : Entails.eval a c2902 := h 2901 (by decide)
  have h4 : Entails.eval a c3438 := h 3437 (by decide)
  have h5 : Entails.eval a c5123 := h 5122 (by decide)
  have h6 : Entails.eval a c2512 := h 2511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8368 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨56, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8367, some c492, some c432, some c1517, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8368 : lratChecker f8368 p8368 = .success := by decide +kernel
theorem unsat8368 : Unsatisfiable (PosFin 65) f8368 := by
  apply lratCheckerSound f8368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8368
  · intro a ha; simp [p8368] at ha; subst a; trivial
  · exact checked8368
theorem derived8368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8368 := by
  apply localUnsat_implies_entails f8368 [c8269, c8367, c492, c432, c1517] c8368 unsat8368 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8367 := derived8367 a h
  have h2 : Entails.eval a c492 := h 491 (by decide)
  have h3 : Entails.eval a c432 := h 431 (by decide)
  have h4 : Entails.eval a c1517 := h 1516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8369 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6680, some c8366, some c6819, some c7165, some c6518, some c6802, some c7328, some c8342, some c8269, some c8283, some c7065, some c8368, some c515, some c523, some c470, some c3116, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8369 : lratChecker f8369 p8369 = .success := by decide +kernel
theorem unsat8369 : Unsatisfiable (PosFin 65) f8369 := by
  apply lratCheckerSound f8369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8369
  · intro a ha; simp [p8369] at ha; subst a; trivial
  · exact checked8369
theorem derived8369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8369 := by
  apply localUnsat_implies_entails f8369 [c6680, c8366, c6819, c7165, c6518, c6802, c7328, c8342, c8269, c8283, c7065, c8368, c515, c523, c470, c3116] c8369 unsat8369 (by rfl) a
  have h0 : Entails.eval a c6680 := h 6679 (by decide)
  have h1 : Entails.eval a c8366 := derived8366 a h
  have h2 : Entails.eval a c6819 := h 6818 (by decide)
  have h3 : Entails.eval a c7165 := h 7164 (by decide)
  have h4 : Entails.eval a c6518 := h 6517 (by decide)
  have h5 : Entails.eval a c6802 := h 6801 (by decide)
  have h6 : Entails.eval a c7328 := h 7327 (by decide)
  have h7 : Entails.eval a c8342 := derived8342 a h
  have h8 : Entails.eval a c8269 := derived8269 a h
  have h9 : Entails.eval a c8283 := derived8283 a h
  have h10 : Entails.eval a c7065 := h 7064 (by decide)
  have h11 : Entails.eval a c8368 := derived8368 a h
  have h12 : Entails.eval a c515 := h 514 (by decide)
  have h13 : Entails.eval a c523 := h 522 (by decide)
  have h14 : Entails.eval a c470 := h 469 (by decide)
  have h15 : Entails.eval a c3116 := h 3115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8370 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c6819, some c6802, some c7328, some c523, some c470, some c516, some c3116, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8370 : lratChecker f8370 p8370 = .success := by decide +kernel
theorem unsat8370 : Unsatisfiable (PosFin 65) f8370 := by
  apply lratCheckerSound f8370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8370
  · intro a ha; simp [p8370] at ha; subst a; trivial
  · exact checked8370
theorem derived8370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8370 := by
  apply localUnsat_implies_entails f8370 [c8366, c6819, c6802, c7328, c523, c470, c516, c3116] c8370 unsat8370 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c6819 := h 6818 (by decide)
  have h2 : Entails.eval a c6802 := h 6801 (by decide)
  have h3 : Entails.eval a c7328 := h 7327 (by decide)
  have h4 : Entails.eval a c523 := h 522 (by decide)
  have h5 : Entails.eval a c470 := h 469 (by decide)
  have h6 : Entails.eval a c516 := h 515 (by decide)
  have h7 : Entails.eval a c3116 := h 3115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8371 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨62, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c3470, some c3476, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8371 : lratChecker f8371 p8371 = .success := by decide +kernel
theorem unsat8371 : Unsatisfiable (PosFin 65) f8371 := by
  apply lratCheckerSound f8371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8371
  · intro a ha; simp [p8371] at ha; subst a; trivial
  · exact checked8371
theorem derived8371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8371 := by
  apply localUnsat_implies_entails f8371 [c8269, c7994, c3470, c3476] c8371 unsat8371 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c3470 := h 3469 (by decide)
  have h3 : Entails.eval a c3476 := h 3475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8372 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c3116, some c456, some c2478, some c2511, some c5085, some c4466, some c5107, some c8051, some c8371, some c3801, some c3645, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8372 : lratChecker f8372 p8372 = .success := by decide +kernel
theorem unsat8372 : Unsatisfiable (PosFin 65) f8372 := by
  apply lratCheckerSound f8372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8372
  · intro a ha; simp [p8372] at ha; subst a; trivial
  · exact checked8372
theorem derived8372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8372 := by
  apply localUnsat_implies_entails f8372 [c8269, c7994, c3116, c456, c2478, c2511, c5085, c4466, c5107, c8051, c8371, c3801, c3645] c8372 unsat8372 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c3116 := h 3115 (by decide)
  have h3 : Entails.eval a c456 := h 455 (by decide)
  have h4 : Entails.eval a c2478 := h 2477 (by decide)
  have h5 : Entails.eval a c2511 := h 2510 (by decide)
  have h6 : Entails.eval a c5085 := h 5084 (by decide)
  have h7 : Entails.eval a c4466 := h 4465 (by decide)
  have h8 : Entails.eval a c5107 := h 5106 (by decide)
  have h9 : Entails.eval a c8051 := derived8051 a h
  have h10 : Entails.eval a c8371 := derived8371 a h
  have h11 : Entails.eval a c3801 := h 3800 (by decide)
  have h12 : Entails.eval a c3645 := h 3644 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8373 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8372, some c449, some c2478, some c2511, some c4418, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8373 : lratChecker f8373 p8373 = .success := by decide +kernel
theorem unsat8373 : Unsatisfiable (PosFin 65) f8373 := by
  apply lratCheckerSound f8373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8373
  · intro a ha; simp [p8373] at ha; subst a; trivial
  · exact checked8373
theorem derived8373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8373 := by
  apply localUnsat_implies_entails f8373 [c8372, c449, c2478, c2511, c4418] c8373 unsat8373 (by rfl) a
  have h0 : Entails.eval a c8372 := derived8372 a h
  have h1 : Entails.eval a c449 := h 448 (by decide)
  have h2 : Entails.eval a c2478 := h 2477 (by decide)
  have h3 : Entails.eval a c2511 := h 2510 (by decide)
  have h4 : Entails.eval a c4418 := h 4417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8374 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1502, some c4339, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8374 : lratChecker f8374 p8374 = .success := by decide +kernel
theorem unsat8374 : Unsatisfiable (PosFin 65) f8374 := by
  apply lratCheckerSound f8374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8374
  · intro a ha; simp [p8374] at ha; subst a; trivial
  · exact checked8374
theorem derived8374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8374 := by
  apply localUnsat_implies_entails f8374 [c8269, c1502, c4339] c8374 unsat8374 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1502 := h 1501 (by decide)
  have h2 : Entails.eval a c4339 := h 4338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8375 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c8300, some c7994, some c8342, some c6802, some c6819, some c7165, some c7328, some c6717, some c6518, some c6680, some c8369, some c8333, some c8370, some c8373, some c421, some c1577, some c3438, some c3408, some c4466, some c8374, some c537, some c3983, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked8375 : lratChecker f8375 p8375 = .success := by decide +kernel
theorem unsat8375 : Unsatisfiable (PosFin 65) f8375 := by
  apply lratCheckerSound f8375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8375
  · intro a ha; simp [p8375] at ha; subst a; trivial
  · exact checked8375
theorem derived8375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8375 := by
  apply localUnsat_implies_entails f8375 [c8366, c8300, c7994, c8342, c6802, c6819, c7165, c7328, c6717, c6518, c6680, c8369, c8333, c8370, c8373, c421, c1577, c3438, c3408, c4466, c8374, c537, c3983] c8375 unsat8375 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8342 := derived8342 a h
  have h4 : Entails.eval a c6802 := h 6801 (by decide)
  have h5 : Entails.eval a c6819 := h 6818 (by decide)
  have h6 : Entails.eval a c7165 := h 7164 (by decide)
  have h7 : Entails.eval a c7328 := h 7327 (by decide)
  have h8 : Entails.eval a c6717 := h 6716 (by decide)
  have h9 : Entails.eval a c6518 := h 6517 (by decide)
  have h10 : Entails.eval a c6680 := h 6679 (by decide)
  have h11 : Entails.eval a c8369 := derived8369 a h
  have h12 : Entails.eval a c8333 := derived8333 a h
  have h13 : Entails.eval a c8370 := derived8370 a h
  have h14 : Entails.eval a c8373 := derived8373 a h
  have h15 : Entails.eval a c421 := h 420 (by decide)
  have h16 : Entails.eval a c1577 := h 1576 (by decide)
  have h17 : Entails.eval a c3438 := h 3437 (by decide)
  have h18 : Entails.eval a c3408 := h 3407 (by decide)
  have h19 : Entails.eval a c4466 := h 4465 (by decide)
  have h20 : Entails.eval a c8374 := derived8374 a h
  have h21 : Entails.eval a c537 := h 536 (by decide)
  have h22 : Entails.eval a c3983 := h 3982 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8376 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c8375, some c7218, some c6631, some c6740, some c6657, some c6933, some c7312, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8376 : lratChecker f8376 p8376 = .success := by decide +kernel
theorem unsat8376 : Unsatisfiable (PosFin 65) f8376 := by
  apply lratCheckerSound f8376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8376
  · intro a ha; simp [p8376] at ha; subst a; trivial
  · exact checked8376
theorem derived8376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8376 := by
  apply localUnsat_implies_entails f8376 [c8366, c8375, c7218, c6631, c6740, c6657, c6933, c7312] c8376 unsat8376 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c8375 := derived8375 a h
  have h2 : Entails.eval a c7218 := h 7217 (by decide)
  have h3 : Entails.eval a c6631 := h 6630 (by decide)
  have h4 : Entails.eval a c6740 := h 6739 (by decide)
  have h5 : Entails.eval a c6657 := h 6656 (by decide)
  have h6 : Entails.eval a c6933 := h 6932 (by decide)
  have h7 : Entails.eval a c7312 := h 7311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8377 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c8300, some c8269, some c7994, some c8376, some c8329, some c8327, some c8340, some c6802, some c6819, some c7328, some c6733, some c8369, some c8333, some c7269, some c7263, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8377 : lratChecker f8377 p8377 = .success := by decide +kernel
theorem unsat8377 : Unsatisfiable (PosFin 65) f8377 := by
  apply lratCheckerSound f8377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8377
  · intro a ha; simp [p8377] at ha; subst a; trivial
  · exact checked8377
theorem derived8377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8377 := by
  apply localUnsat_implies_entails f8377 [c8366, c8300, c8269, c7994, c8376, c8329, c8327, c8340, c6802, c6819, c7328, c6733, c8369, c8333, c7269, c7263] c8377 unsat8377 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8376 := derived8376 a h
  have h5 : Entails.eval a c8329 := derived8329 a h
  have h6 : Entails.eval a c8327 := derived8327 a h
  have h7 : Entails.eval a c8340 := derived8340 a h
  have h8 : Entails.eval a c6802 := h 6801 (by decide)
  have h9 : Entails.eval a c6819 := h 6818 (by decide)
  have h10 : Entails.eval a c7328 := h 7327 (by decide)
  have h11 : Entails.eval a c6733 := h 6732 (by decide)
  have h12 : Entails.eval a c8369 := derived8369 a h
  have h13 : Entails.eval a c8333 := derived8333 a h
  have h14 : Entails.eval a c7269 := h 7268 (by decide)
  have h15 : Entails.eval a c7263 := h 7262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8378 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c8366, some c8342, some c6802, some c6819, some c7450, some c7287, some c6733, some c6657, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8378 : lratChecker f8378 p8378 = .success := by decide +kernel
theorem unsat8378 : Unsatisfiable (PosFin 65) f8378 := by
  apply lratCheckerSound f8378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8378
  · intro a ha; simp [p8378] at ha; subst a; trivial
  · exact checked8378
theorem derived8378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8378 := by
  apply localUnsat_implies_entails f8378 [c8377, c8366, c8342, c6802, c6819, c7450, c7287, c6733, c6657] c8378 unsat8378 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c8366 := derived8366 a h
  have h2 : Entails.eval a c8342 := derived8342 a h
  have h3 : Entails.eval a c6802 := h 6801 (by decide)
  have h4 : Entails.eval a c6819 := h 6818 (by decide)
  have h5 : Entails.eval a c7450 := h 7449 (by decide)
  have h6 : Entails.eval a c7287 := h 7286 (by decide)
  have h7 : Entails.eval a c6733 := h 6732 (by decide)
  have h8 : Entails.eval a c6657 := h 6656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8379 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8329, some c8327, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8379 : lratChecker f8379 p8379 = .success := by decide +kernel
theorem unsat8379 : Unsatisfiable (PosFin 65) f8379 := by
  apply lratCheckerSound f8379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8379
  · intro a ha; simp [p8379] at ha; subst a; trivial
  · exact checked8379
theorem derived8379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8379 := by
  apply localUnsat_implies_entails f8379 [c8329, c8327] c8379 unsat8379 (by rfl) a
  have h0 : Entails.eval a c8329 := derived8329 a h
  have h1 : Entails.eval a c8327 := derived8327 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8380 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c8377, some c8378, some c8379, some c7477, some c7463, some c6933, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8380 : lratChecker f8380 p8380 = .success := by decide +kernel
theorem unsat8380 : Unsatisfiable (PosFin 65) f8380 := by
  apply lratCheckerSound f8380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8380
  · intro a ha; simp [p8380] at ha; subst a; trivial
  · exact checked8380
theorem derived8380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8380 := by
  apply localUnsat_implies_entails f8380 [c8366, c8377, c8378, c8379, c7477, c7463, c6933] c8380 unsat8380 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8378 := derived8378 a h
  have h3 : Entails.eval a c8379 := derived8379 a h
  have h4 : Entails.eval a c7477 := h 7476 (by decide)
  have h5 : Entails.eval a c7463 := h 7462 (by decide)
  have h6 : Entails.eval a c6933 := h 6932 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8381 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2495, some c1389, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p8381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8381 : lratChecker f8381 p8381 = .success := by decide +kernel
theorem unsat8381 : Unsatisfiable (PosFin 65) f8381 := by
  apply lratCheckerSound f8381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8381
  · intro a ha; simp [p8381] at ha; subst a; trivial
  · exact checked8381
theorem derived8381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8381 := by
  apply localUnsat_implies_entails f8381 [c2495, c1389] c8381 unsat8381 (by rfl) a
  have h0 : Entails.eval a c2495 := h 2494 (by decide)
  have h1 : Entails.eval a c1389 := h 1388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8382 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8300, some c8269, some c8381, some c1366, some c2479, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8382 : lratChecker f8382 p8382 = .success := by decide +kernel
theorem unsat8382 : Unsatisfiable (PosFin 65) f8382 := by
  apply lratCheckerSound f8382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8382
  · intro a ha; simp [p8382] at ha; subst a; trivial
  · exact checked8382
theorem derived8382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8382 := by
  apply localUnsat_implies_entails f8382 [c8380, c8300, c8269, c8381, c1366, c2479] c8382 unsat8382 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c8381 := derived8381 a h
  have h4 : Entails.eval a c1366 := h 1365 (by decide)
  have h5 : Entails.eval a c2479 := h 2478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8383 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8300, some c8269, some c8382, some c2442, some c2438, some c2949, some c3009, some c2479, some c4393, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p8383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8383 : lratChecker f8383 p8383 = .success := by decide +kernel
theorem unsat8383 : Unsatisfiable (PosFin 65) f8383 := by
  apply lratCheckerSound f8383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8383
  · intro a ha; simp [p8383] at ha; subst a; trivial
  · exact checked8383
theorem derived8383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8383 := by
  apply localUnsat_implies_entails f8383 [c8380, c8300, c8269, c8382, c2442, c2438, c2949, c3009, c2479, c4393] c8383 unsat8383 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8300 := derived8300 a h
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c8382 := derived8382 a h
  have h4 : Entails.eval a c2442 := h 2441 (by decide)
  have h5 : Entails.eval a c2438 := h 2437 (by decide)
  have h6 : Entails.eval a c2949 := h 2948 (by decide)
  have h7 : Entails.eval a c3009 := h 3008 (by decide)
  have h8 : Entails.eval a c2479 := h 2478 (by decide)
  have h9 : Entails.eval a c4393 := h 4392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8384 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨59, by decide⟩, false), (⟨56, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1384, some c1387, some c1379, some c1380, some c1371, some c1376, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8384 : lratChecker f8384 p8384 = .success := by decide +kernel
theorem unsat8384 : Unsatisfiable (PosFin 65) f8384 := by
  apply lratCheckerSound f8384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8384
  · intro a ha; simp [p8384] at ha; subst a; trivial
  · exact checked8384
theorem derived8384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8384 := by
  apply localUnsat_implies_entails f8384 [c1384, c1387, c1379, c1380, c1371, c1376] c8384 unsat8384 (by rfl) a
  have h0 : Entails.eval a c1384 := h 1383 (by decide)
  have h1 : Entails.eval a c1387 := h 1386 (by decide)
  have h2 : Entails.eval a c1379 := h 1378 (by decide)
  have h3 : Entails.eval a c1380 := h 1379 (by decide)
  have h4 : Entails.eval a c1371 := h 1370 (by decide)
  have h5 : Entails.eval a c1376 := h 1375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8385 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨56, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1365, some c1395, some c1396, some c1370, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8385 : lratChecker f8385 p8385 = .success := by decide +kernel
theorem unsat8385 : Unsatisfiable (PosFin 65) f8385 := by
  apply lratCheckerSound f8385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8385
  · intro a ha; simp [p8385] at ha; subst a; trivial
  · exact checked8385
theorem derived8385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8385 := by
  apply localUnsat_implies_entails f8385 [c1365, c1395, c1396, c1370] c8385 unsat8385 (by rfl) a
  have h0 : Entails.eval a c1365 := h 1364 (by decide)
  have h1 : Entails.eval a c1395 := h 1394 (by decide)
  have h2 : Entails.eval a c1396 := h 1395 (by decide)
  have h3 : Entails.eval a c1370 := h 1369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8386 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1067, some c2605, some c2607, some c4382, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8386 : lratChecker f8386 p8386 = .success := by decide +kernel
theorem unsat8386 : Unsatisfiable (PosFin 65) f8386 := by
  apply lratCheckerSound f8386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8386
  · intro a ha; simp [p8386] at ha; subst a; trivial
  · exact checked8386
theorem derived8386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8386 := by
  apply localUnsat_implies_entails f8386 [c1067, c2605, c2607, c4382] c8386 unsat8386 (by rfl) a
  have h0 : Entails.eval a c1067 := h 1066 (by decide)
  have h1 : Entails.eval a c2605 := h 2604 (by decide)
  have h2 : Entails.eval a c2607 := h 2606 (by decide)
  have h3 : Entails.eval a c4382 := h 4381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8387 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1313, some c1314, some c1337, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8387 : lratChecker f8387 p8387 = .success := by decide +kernel
theorem unsat8387 : Unsatisfiable (PosFin 65) f8387 := by
  apply lratCheckerSound f8387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8387
  · intro a ha; simp [p8387] at ha; subst a; trivial
  · exact checked8387
theorem derived8387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8387 := by
  apply localUnsat_implies_entails f8387 [c1313, c1314, c1337] c8387 unsat8387 (by rfl) a
  have h0 : Entails.eval a c1313 := h 1312 (by decide)
  have h1 : Entails.eval a c1314 := h 1313 (by decide)
  have h2 : Entails.eval a c1337 := h 1336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8388 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨63, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, true), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3586, some c3791, some c4662, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8388 : lratChecker f8388 p8388 = .success := by decide +kernel
theorem unsat8388 : Unsatisfiable (PosFin 65) f8388 := by
  apply lratCheckerSound f8388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8388
  · intro a ha; simp [p8388] at ha; subst a; trivial
  · exact checked8388
theorem derived8388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8388 := by
  apply localUnsat_implies_entails f8388 [c3586, c3791, c4662] c8388 unsat8388 (by rfl) a
  have h0 : Entails.eval a c3586 := h 3585 (by decide)
  have h1 : Entails.eval a c3791 := h 3790 (by decide)
  have h2 : Entails.eval a c4662 := h 4661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8389 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1326, some c2080, some c1068, some c1075, some c1328, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8389 : lratChecker f8389 p8389 = .success := by decide +kernel
theorem unsat8389 : Unsatisfiable (PosFin 65) f8389 := by
  apply lratCheckerSound f8389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8389
  · intro a ha; simp [p8389] at ha; subst a; trivial
  · exact checked8389
theorem derived8389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8389 := by
  apply localUnsat_implies_entails f8389 [c1326, c2080, c1068, c1075, c1328] c8389 unsat8389 (by rfl) a
  have h0 : Entails.eval a c1326 := h 1325 (by decide)
  have h1 : Entails.eval a c2080 := h 2079 (by decide)
  have h2 : Entails.eval a c1068 := h 1067 (by decide)
  have h3 : Entails.eval a c1075 := h 1074 (by decide)
  have h4 : Entails.eval a c1328 := h 1327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8390 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8385, some c1387, some c1384, some c1379, some c1380, some c1376, some c8384, some c1381, some c8007, some c1385, some c8387, some c1326, some c8389, some c8388, some c653, some c598, some c628, some c689, some c621, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8390 : lratChecker f8390 p8390 = .success := by decide +kernel
theorem unsat8390 : Unsatisfiable (PosFin 65) f8390 := by
  apply lratCheckerSound f8390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8390
  · intro a ha; simp [p8390] at ha; subst a; trivial
  · exact checked8390
theorem derived8390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8390 := by
  apply localUnsat_implies_entails f8390 [c8380, c8385, c1387, c1384, c1379, c1380, c1376, c8384, c1381, c8007, c1385, c8387, c1326, c8389, c8388, c653, c598, c628, c689, c621] c8390 unsat8390 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8385 := derived8385 a h
  have h2 : Entails.eval a c1387 := h 1386 (by decide)
  have h3 : Entails.eval a c1384 := h 1383 (by decide)
  have h4 : Entails.eval a c1379 := h 1378 (by decide)
  have h5 : Entails.eval a c1380 := h 1379 (by decide)
  have h6 : Entails.eval a c1376 := h 1375 (by decide)
  have h7 : Entails.eval a c8384 := derived8384 a h
  have h8 : Entails.eval a c1381 := h 1380 (by decide)
  have h9 : Entails.eval a c8007 := derived8007 a h
  have h10 : Entails.eval a c1385 := h 1384 (by decide)
  have h11 : Entails.eval a c8387 := derived8387 a h
  have h12 : Entails.eval a c1326 := h 1325 (by decide)
  have h13 : Entails.eval a c8389 := derived8389 a h
  have h14 : Entails.eval a c8388 := derived8388 a h
  have h15 : Entails.eval a c653 := h 652 (by decide)
  have h16 : Entails.eval a c598 := h 597 (by decide)
  have h17 : Entails.eval a c628 := h 627 (by decide)
  have h18 : Entails.eval a c689 := h 688 (by decide)
  have h19 : Entails.eval a c621 := h 620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8391 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c382, some c383, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8391 : lratChecker f8391 p8391 = .success := by decide +kernel
theorem unsat8391 : Unsatisfiable (PosFin 65) f8391 := by
  apply lratCheckerSound f8391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8391
  · intro a ha; simp [p8391] at ha; subst a; trivial
  · exact checked8391
theorem derived8391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8391 := by
  apply localUnsat_implies_entails f8391 [c382, c383] c8391 unsat8391 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8392 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8385, some c1384, some c1387, some c8384, some c1379, some c1381, some c1380, some c8007, some c1376, some c8390, some c1317, some c1308, some c1318, some c1327, some c1342, some c1307, some c1313, some c1314, some c1340, some c1345, some c1349, some c1352, some c8391, some c5406, some c6056, some c5454, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked8392 : lratChecker f8392 p8392 = .success := by decide +kernel
theorem unsat8392 : Unsatisfiable (PosFin 65) f8392 := by
  apply lratCheckerSound f8392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8392
  · intro a ha; simp [p8392] at ha; subst a; trivial
  · exact checked8392
theorem derived8392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8392 := by
  apply localUnsat_implies_entails f8392 [c8380, c8385, c1384, c1387, c8384, c1379, c1381, c1380, c8007, c1376, c8390, c1317, c1308, c1318, c1327, c1342, c1307, c1313, c1314, c1340, c1345, c1349, c1352, c8391, c5406, c6056, c5454] c8392 unsat8392 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8385 := derived8385 a h
  have h2 : Entails.eval a c1384 := h 1383 (by decide)
  have h3 : Entails.eval a c1387 := h 1386 (by decide)
  have h4 : Entails.eval a c8384 := derived8384 a h
  have h5 : Entails.eval a c1379 := h 1378 (by decide)
  have h6 : Entails.eval a c1381 := h 1380 (by decide)
  have h7 : Entails.eval a c1380 := h 1379 (by decide)
  have h8 : Entails.eval a c8007 := derived8007 a h
  have h9 : Entails.eval a c1376 := h 1375 (by decide)
  have h10 : Entails.eval a c8390 := derived8390 a h
  have h11 : Entails.eval a c1317 := h 1316 (by decide)
  have h12 : Entails.eval a c1308 := h 1307 (by decide)
  have h13 : Entails.eval a c1318 := h 1317 (by decide)
  have h14 : Entails.eval a c1327 := h 1326 (by decide)
  have h15 : Entails.eval a c1342 := h 1341 (by decide)
  have h16 : Entails.eval a c1307 := h 1306 (by decide)
  have h17 : Entails.eval a c1313 := h 1312 (by decide)
  have h18 : Entails.eval a c1314 := h 1313 (by decide)
  have h19 : Entails.eval a c1340 := h 1339 (by decide)
  have h20 : Entails.eval a c1345 := h 1344 (by decide)
  have h21 : Entails.eval a c1349 := h 1348 (by decide)
  have h22 : Entails.eval a c1352 := h 1351 (by decide)
  have h23 : Entails.eval a c8391 := derived8391 a h
  have h24 : Entails.eval a c5406 := h 5405 (by decide)
  have h25 : Entails.eval a c6056 := h 6055 (by decide)
  have h26 : Entails.eval a c5454 := h 5453 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8393 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨64, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8007, some c1370, some c2177, some c2110, some c4633, some c3581, some c3584, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8393 : lratChecker f8393 p8393 = .success := by decide +kernel
theorem unsat8393 : Unsatisfiable (PosFin 65) f8393 := by
  apply lratCheckerSound f8393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8393
  · intro a ha; simp [p8393] at ha; subst a; trivial
  · exact checked8393
theorem derived8393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8393 := by
  apply localUnsat_implies_entails f8393 [c8007, c1370, c2177, c2110, c4633, c3581, c3584] c8393 unsat8393 (by rfl) a
  have h0 : Entails.eval a c8007 := derived8007 a h
  have h1 : Entails.eval a c1370 := h 1369 (by decide)
  have h2 : Entails.eval a c2177 := h 2176 (by decide)
  have h3 : Entails.eval a c2110 := h 2109 (by decide)
  have h4 : Entails.eval a c4633 := h 4632 (by decide)
  have h5 : Entails.eval a c3581 := h 3580 (by decide)
  have h6 : Entails.eval a c3584 := h 3583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8394 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨62, by decide⟩, false), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨55, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1105, some c1112, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8394 : lratChecker f8394 p8394 = .success := by decide +kernel
theorem unsat8394 : Unsatisfiable (PosFin 65) f8394 := by
  apply lratCheckerSound f8394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8394
  · intro a ha; simp [p8394] at ha; subst a; trivial
  · exact checked8394
theorem derived8394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8394 := by
  apply localUnsat_implies_entails f8394 [c1105, c1112] c8394 unsat8394 (by rfl) a
  have h0 : Entails.eval a c1105 := h 1104 (by decide)
  have h1 : Entails.eval a c1112 := h 1111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8395 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1331, some c1332, some c1335, some c1351, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8395 : lratChecker f8395 p8395 = .success := by decide +kernel
theorem unsat8395 : Unsatisfiable (PosFin 65) f8395 := by
  apply lratCheckerSound f8395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8395
  · intro a ha; simp [p8395] at ha; subst a; trivial
  · exact checked8395
theorem derived8395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8395 := by
  apply localUnsat_implies_entails f8395 [c1331, c1332, c1335, c1351] c8395 unsat8395 (by rfl) a
  have h0 : Entails.eval a c1331 := h 1330 (by decide)
  have h1 : Entails.eval a c1332 := h 1331 (by decide)
  have h2 : Entails.eval a c1335 := h 1334 (by decide)
  have h3 : Entails.eval a c1351 := h 1350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8396 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨61, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1324, some c1323, some c1348, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8396 : lratChecker f8396 p8396 = .success := by decide +kernel
theorem unsat8396 : Unsatisfiable (PosFin 65) f8396 := by
  apply lratCheckerSound f8396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8396
  · intro a ha; simp [p8396] at ha; subst a; trivial
  · exact checked8396
theorem derived8396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8396 := by
  apply localUnsat_implies_entails f8396 [c1324, c1323, c1348] c8396 unsat8396 (by rfl) a
  have h0 : Entails.eval a c1324 := h 1323 (by decide)
  have h1 : Entails.eval a c1323 := h 1322 (by decide)
  have h2 : Entails.eval a c1348 := h 1347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8397 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8395, some c8380, some c1361, some c1379, some c8393, some c1384, some c1348, some c1311, some c1325, some c1340, some c1330, some c1347, some c698, some c1336, some c8391, some c1310, some c7068, some c7062, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8397 : lratChecker f8397 p8397 = .success := by decide +kernel
theorem unsat8397 : Unsatisfiable (PosFin 65) f8397 := by
  apply lratCheckerSound f8397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8397
  · intro a ha; simp [p8397] at ha; subst a; trivial
  · exact checked8397
theorem derived8397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8397 := by
  apply localUnsat_implies_entails f8397 [c8395, c8380, c1361, c1379, c8393, c1384, c1348, c1311, c1325, c1340, c1330, c1347, c698, c1336, c8391, c1310, c7068, c7062] c8397 unsat8397 (by rfl) a
  have h0 : Entails.eval a c8395 := derived8395 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c1361 := h 1360 (by decide)
  have h3 : Entails.eval a c1379 := h 1378 (by decide)
  have h4 : Entails.eval a c8393 := derived8393 a h
  have h5 : Entails.eval a c1384 := h 1383 (by decide)
  have h6 : Entails.eval a c1348 := h 1347 (by decide)
  have h7 : Entails.eval a c1311 := h 1310 (by decide)
  have h8 : Entails.eval a c1325 := h 1324 (by decide)
  have h9 : Entails.eval a c1340 := h 1339 (by decide)
  have h10 : Entails.eval a c1330 := h 1329 (by decide)
  have h11 : Entails.eval a c1347 := h 1346 (by decide)
  have h12 : Entails.eval a c698 := h 697 (by decide)
  have h13 : Entails.eval a c1336 := h 1335 (by decide)
  have h14 : Entails.eval a c8391 := derived8391 a h
  have h15 : Entails.eval a c1310 := h 1309 (by decide)
  have h16 : Entails.eval a c7068 := h 7067 (by decide)
  have h17 : Entails.eval a c7062 := h 7061 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8398 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c1379, some c1384, some c1361, some c8393, some c1375, some c1378, some c8395, some c8396, some c8397, some c657, some c1322, some c1350, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8398 : lratChecker f8398 p8398 = .success := by decide +kernel
theorem unsat8398 : Unsatisfiable (PosFin 65) f8398 := by
  apply lratCheckerSound f8398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8398
  · intro a ha; simp [p8398] at ha; subst a; trivial
  · exact checked8398
theorem derived8398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8398 := by
  apply localUnsat_implies_entails f8398 [c8380, c1379, c1384, c1361, c8393, c1375, c1378, c8395, c8396, c8397, c657, c1322, c1350] c8398 unsat8398 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c1379 := h 1378 (by decide)
  have h2 : Entails.eval a c1384 := h 1383 (by decide)
  have h3 : Entails.eval a c1361 := h 1360 (by decide)
  have h4 : Entails.eval a c8393 := derived8393 a h
  have h5 : Entails.eval a c1375 := h 1374 (by decide)
  have h6 : Entails.eval a c1378 := h 1377 (by decide)
  have h7 : Entails.eval a c8395 := derived8395 a h
  have h8 : Entails.eval a c8396 := derived8396 a h
  have h9 : Entails.eval a c8397 := derived8397 a h
  have h10 : Entails.eval a c657 := h 656 (by decide)
  have h11 : Entails.eval a c1322 := h 1321 (by decide)
  have h12 : Entails.eval a c1350 := h 1349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8399 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3581, some c3788, some c4660, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8399 : lratChecker f8399 p8399 = .success := by decide +kernel
theorem unsat8399 : Unsatisfiable (PosFin 65) f8399 := by
  apply lratCheckerSound f8399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8399
  · intro a ha; simp [p8399] at ha; subst a; trivial
  · exact checked8399
theorem derived8399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8399 := by
  apply localUnsat_implies_entails f8399 [c3581, c3788, c4660] c8399 unsat8399 (by rfl) a
  have h0 : Entails.eval a c3581 := h 3580 (by decide)
  have h1 : Entails.eval a c3788 := h 3787 (by decide)
  have h2 : Entails.eval a c4660 := h 4659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8400 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c1375, some c1378, some c1394, some c1312, some c1324, some c1346, some c1336, some c680, some c1309, some c718, some c1356, some c1355, some c710, some c1354, some c1357, some c712, some c5201, some c720, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8400 : lratChecker f8400 p8400 = .success := by decide +kernel
theorem unsat8400 : Unsatisfiable (PosFin 65) f8400 := by
  apply lratCheckerSound f8400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8400
  · intro a ha; simp [p8400] at ha; subst a; trivial
  · exact checked8400
theorem derived8400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8400 := by
  apply localUnsat_implies_entails f8400 [c8380, c1375, c1378, c1394, c1312, c1324, c1346, c1336, c680, c1309, c718, c1356, c1355, c710, c1354, c1357, c712, c5201, c720] c8400 unsat8400 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c1375 := h 1374 (by decide)
  have h2 : Entails.eval a c1378 := h 1377 (by decide)
  have h3 : Entails.eval a c1394 := h 1393 (by decide)
  have h4 : Entails.eval a c1312 := h 1311 (by decide)
  have h5 : Entails.eval a c1324 := h 1323 (by decide)
  have h6 : Entails.eval a c1346 := h 1345 (by decide)
  have h7 : Entails.eval a c1336 := h 1335 (by decide)
  have h8 : Entails.eval a c680 := h 679 (by decide)
  have h9 : Entails.eval a c1309 := h 1308 (by decide)
  have h10 : Entails.eval a c718 := h 717 (by decide)
  have h11 : Entails.eval a c1356 := h 1355 (by decide)
  have h12 : Entails.eval a c1355 := h 1354 (by decide)
  have h13 : Entails.eval a c710 := h 709 (by decide)
  have h14 : Entails.eval a c1354 := h 1353 (by decide)
  have h15 : Entails.eval a c1357 := h 1356 (by decide)
  have h16 : Entails.eval a c712 := h 711 (by decide)
  have h17 : Entails.eval a c5201 := h 5200 (by decide)
  have h18 : Entails.eval a c720 := h 719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8401 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1334, some c1329, some c1338, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8401 : lratChecker f8401 p8401 = .success := by decide +kernel
theorem unsat8401 : Unsatisfiable (PosFin 65) f8401 := by
  apply lratCheckerSound f8401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8401
  · intro a ha; simp [p8401] at ha; subst a; trivial
  · exact checked8401
theorem derived8401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8401 := by
  apply localUnsat_implies_entails f8401 [c1334, c1329, c1338] c8401 unsat8401 (by rfl) a
  have h0 : Entails.eval a c1334 := h 1333 (by decide)
  have h1 : Entails.eval a c1329 := h 1328 (by decide)
  have h2 : Entails.eval a c1338 := h 1337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8402 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c1385, some c1394, some c1361, some c1379, some c8393, some c1375, some c1378, some c1384, some c8398, some c8401, some c1323, some c8400, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8402 : lratChecker f8402 p8402 = .success := by decide +kernel
theorem unsat8402 : Unsatisfiable (PosFin 65) f8402 := by
  apply lratCheckerSound f8402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8402
  · intro a ha; simp [p8402] at ha; subst a; trivial
  · exact checked8402
theorem derived8402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8402 := by
  apply localUnsat_implies_entails f8402 [c8380, c1385, c1394, c1361, c1379, c8393, c1375, c1378, c1384, c8398, c8401, c1323, c8400] c8402 unsat8402 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c1385 := h 1384 (by decide)
  have h2 : Entails.eval a c1394 := h 1393 (by decide)
  have h3 : Entails.eval a c1361 := h 1360 (by decide)
  have h4 : Entails.eval a c1379 := h 1378 (by decide)
  have h5 : Entails.eval a c8393 := derived8393 a h
  have h6 : Entails.eval a c1375 := h 1374 (by decide)
  have h7 : Entails.eval a c1378 := h 1377 (by decide)
  have h8 : Entails.eval a c1384 := h 1383 (by decide)
  have h9 : Entails.eval a c8398 := derived8398 a h
  have h10 : Entails.eval a c8401 := derived8401 a h
  have h11 : Entails.eval a c1323 := h 1322 (by decide)
  have h12 : Entails.eval a c8400 := derived8400 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8403 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨61, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1341, some c8396, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8403 : lratChecker f8403 p8403 = .success := by decide +kernel
theorem unsat8403 : Unsatisfiable (PosFin 65) f8403 := by
  apply lratCheckerSound f8403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8403
  · intro a ha; simp [p8403] at ha; subst a; trivial
  · exact checked8403
theorem derived8403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8403 := by
  apply localUnsat_implies_entails f8403 [c1341, c8396] c8403 unsat8403 (by rfl) a
  have h0 : Entails.eval a c1341 := h 1340 (by decide)
  have h1 : Entails.eval a c8396 := derived8396 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8404 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨37, by decide⟩, true), (⟨41, by decide⟩, false), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨61, by decide⟩, false), (⟨57, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5869, some c5278, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p8404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8404 : lratChecker f8404 p8404 = .success := by decide +kernel
theorem unsat8404 : Unsatisfiable (PosFin 65) f8404 := by
  apply lratCheckerSound f8404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8404
  · intro a ha; simp [p8404] at ha; subst a; trivial
  · exact checked8404
theorem derived8404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8404 := by
  apply localUnsat_implies_entails f8404 [c5869, c5278] c8404 unsat8404 (by rfl) a
  have h0 : Entails.eval a c5869 := h 5868 (by decide)
  have h1 : Entails.eval a c5278 := h 5277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8405 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c1385, some c1394, some c1361, some c1379, some c1384, some c8393, some c1375, some c1378, some c8394, some c8399, some c8402, some c8403, some c8395, some c1326, some c653, some c1312, some c1324, some c1323, some c1346, some c1343, some c680, some c1309, some c718, some c1356, some c1355, some c710, some c1354, some c1357, some c1358, some c714, some c8404, some c5508, some c5697, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked8405 : lratChecker f8405 p8405 = .success := by decide +kernel
theorem unsat8405 : Unsatisfiable (PosFin 65) f8405 := by
  apply lratCheckerSound f8405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8405
  · intro a ha; simp [p8405] at ha; subst a; trivial
  · exact checked8405
theorem derived8405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8405 := by
  apply localUnsat_implies_entails f8405 [c8380, c1385, c1394, c1361, c1379, c1384, c8393, c1375, c1378, c8394, c8399, c8402, c8403, c8395, c1326, c653, c1312, c1324, c1323, c1346, c1343, c680, c1309, c718, c1356, c1355, c710, c1354, c1357, c1358, c714, c8404, c5508, c5697] c8405 unsat8405 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c1385 := h 1384 (by decide)
  have h2 : Entails.eval a c1394 := h 1393 (by decide)
  have h3 : Entails.eval a c1361 := h 1360 (by decide)
  have h4 : Entails.eval a c1379 := h 1378 (by decide)
  have h5 : Entails.eval a c1384 := h 1383 (by decide)
  have h6 : Entails.eval a c8393 := derived8393 a h
  have h7 : Entails.eval a c1375 := h 1374 (by decide)
  have h8 : Entails.eval a c1378 := h 1377 (by decide)
  have h9 : Entails.eval a c8394 := derived8394 a h
  have h10 : Entails.eval a c8399 := derived8399 a h
  have h11 : Entails.eval a c8402 := derived8402 a h
  have h12 : Entails.eval a c8403 := derived8403 a h
  have h13 : Entails.eval a c8395 := derived8395 a h
  have h14 : Entails.eval a c1326 := h 1325 (by decide)
  have h15 : Entails.eval a c653 := h 652 (by decide)
  have h16 : Entails.eval a c1312 := h 1311 (by decide)
  have h17 : Entails.eval a c1324 := h 1323 (by decide)
  have h18 : Entails.eval a c1323 := h 1322 (by decide)
  have h19 : Entails.eval a c1346 := h 1345 (by decide)
  have h20 : Entails.eval a c1343 := h 1342 (by decide)
  have h21 : Entails.eval a c680 := h 679 (by decide)
  have h22 : Entails.eval a c1309 := h 1308 (by decide)
  have h23 : Entails.eval a c718 := h 717 (by decide)
  have h24 : Entails.eval a c1356 := h 1355 (by decide)
  have h25 : Entails.eval a c1355 := h 1354 (by decide)
  have h26 : Entails.eval a c710 := h 709 (by decide)
  have h27 : Entails.eval a c1354 := h 1353 (by decide)
  have h28 : Entails.eval a c1357 := h 1356 (by decide)
  have h29 : Entails.eval a c1358 := h 1357 (by decide)
  have h30 : Entails.eval a c714 := h 713 (by decide)
  have h31 : Entails.eval a c8404 := derived8404 a h
  have h32 : Entails.eval a c5508 := h 5507 (by decide)
  have h33 : Entails.eval a c5697 := h 5696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8406 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨60, by decide⟩, false), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8399, some c3785, some c3578, some c4655, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8406 : lratChecker f8406 p8406 = .success := by decide +kernel
theorem unsat8406 : Unsatisfiable (PosFin 65) f8406 := by
  apply lratCheckerSound f8406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8406
  · intro a ha; simp [p8406] at ha; subst a; trivial
  · exact checked8406
theorem derived8406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8406 := by
  apply localUnsat_implies_entails f8406 [c8399, c3785, c3578, c4655] c8406 unsat8406 (by rfl) a
  have h0 : Entails.eval a c8399 := derived8399 a h
  have h1 : Entails.eval a c3785 := h 3784 (by decide)
  have h2 : Entails.eval a c3578 := h 3577 (by decide)
  have h3 : Entails.eval a c4655 := h 4654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8407 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8392, some c8405, some c1387, some c1386, some c1374, some c1375, some c1371, some c1377, some c1394, some c8393, some c8406, some c1105, some c1099, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8407 : lratChecker f8407 p8407 = .success := by decide +kernel
theorem unsat8407 : Unsatisfiable (PosFin 65) f8407 := by
  apply lratCheckerSound f8407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8407
  · intro a ha; simp [p8407] at ha; subst a; trivial
  · exact checked8407
theorem derived8407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8407 := by
  apply localUnsat_implies_entails f8407 [c8380, c8392, c8405, c1387, c1386, c1374, c1375, c1371, c1377, c1394, c8393, c8406, c1105, c1099] c8407 unsat8407 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8392 := derived8392 a h
  have h2 : Entails.eval a c8405 := derived8405 a h
  have h3 : Entails.eval a c1387 := h 1386 (by decide)
  have h4 : Entails.eval a c1386 := h 1385 (by decide)
  have h5 : Entails.eval a c1374 := h 1373 (by decide)
  have h6 : Entails.eval a c1375 := h 1374 (by decide)
  have h7 : Entails.eval a c1371 := h 1370 (by decide)
  have h8 : Entails.eval a c1377 := h 1376 (by decide)
  have h9 : Entails.eval a c1394 := h 1393 (by decide)
  have h10 : Entails.eval a c8393 := derived8393 a h
  have h11 : Entails.eval a c8406 := derived8406 a h
  have h12 : Entails.eval a c1105 := h 1104 (by decide)
  have h13 : Entails.eval a c1099 := h 1098 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8408 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1361, some c1379, some c1360, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8408 : lratChecker f8408 p8408 = .success := by decide +kernel
theorem unsat8408 : Unsatisfiable (PosFin 65) f8408 := by
  apply lratCheckerSound f8408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8408
  · intro a ha; simp [p8408] at ha; subst a; trivial
  · exact checked8408
theorem derived8408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8408 := by
  apply localUnsat_implies_entails f8408 [c1361, c1379, c1360] c8408 unsat8408 (by rfl) a
  have h0 : Entails.eval a c1361 := h 1360 (by decide)
  have h1 : Entails.eval a c1379 := h 1378 (by decide)
  have h2 : Entails.eval a c1360 := h 1359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8409 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1390, some c1388, some c8385, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8409 : lratChecker f8409 p8409 = .success := by decide +kernel
theorem unsat8409 : Unsatisfiable (PosFin 65) f8409 := by
  apply lratCheckerSound f8409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8409
  · intro a ha; simp [p8409] at ha; subst a; trivial
  · exact checked8409
theorem derived8409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8409 := by
  apply localUnsat_implies_entails f8409 [c1390, c1388, c8385] c8409 unsat8409 (by rfl) a
  have h0 : Entails.eval a c1390 := h 1389 (by decide)
  have h1 : Entails.eval a c1388 := h 1387 (by decide)
  have h2 : Entails.eval a c8385 := derived8385 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8410 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨59, by decide⟩, false), (⟨57, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1326, some c2080, some c2078, some c2090, some c814, some c1081, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8410 : lratChecker f8410 p8410 = .success := by decide +kernel
theorem unsat8410 : Unsatisfiable (PosFin 65) f8410 := by
  apply lratCheckerSound f8410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8410
  · intro a ha; simp [p8410] at ha; subst a; trivial
  · exact checked8410
theorem derived8410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8410 := by
  apply localUnsat_implies_entails f8410 [c1326, c2080, c2078, c2090, c814, c1081] c8410 unsat8410 (by rfl) a
  have h0 : Entails.eval a c1326 := h 1325 (by decide)
  have h1 : Entails.eval a c2080 := h 2079 (by decide)
  have h2 : Entails.eval a c2078 := h 2077 (by decide)
  have h3 : Entails.eval a c2090 := h 2089 (by decide)
  have h4 : Entails.eval a c814 := h 813 (by decide)
  have h5 : Entails.eval a c1081 := h 1080 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8411 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨59, by decide⟩, false), (⟨57, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8410, some c1316, some c1315, some c8395, some c1344, some c1339, some c1079, some c1077, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8411 : lratChecker f8411 p8411 = .success := by decide +kernel
theorem unsat8411 : Unsatisfiable (PosFin 65) f8411 := by
  apply lratCheckerSound f8411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8411
  · intro a ha; simp [p8411] at ha; subst a; trivial
  · exact checked8411
theorem derived8411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8411 := by
  apply localUnsat_implies_entails f8411 [c8410, c1316, c1315, c8395, c1344, c1339, c1079, c1077] c8411 unsat8411 (by rfl) a
  have h0 : Entails.eval a c8410 := derived8410 a h
  have h1 : Entails.eval a c1316 := h 1315 (by decide)
  have h2 : Entails.eval a c1315 := h 1314 (by decide)
  have h3 : Entails.eval a c8395 := derived8395 a h
  have h4 : Entails.eval a c1344 := h 1343 (by decide)
  have h5 : Entails.eval a c1339 := h 1338 (by decide)
  have h6 : Entails.eval a c1079 := h 1078 (by decide)
  have h7 : Entails.eval a c1077 := h 1076 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8412 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8409, some c8408, some c1389, some c1373, some c8296, some c1382, some c1377, some c1387, some c1360, some c8406, some c1105, some c8411, some c1308, some c1320, some c1319, some c1040, some c1080, some c2093, some c1072, some c1039, some c1333, some c2072, some c1307, some c2095, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked8412 : lratChecker f8412 p8412 = .success := by decide +kernel
theorem unsat8412 : Unsatisfiable (PosFin 65) f8412 := by
  apply lratCheckerSound f8412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8412
  · intro a ha; simp [p8412] at ha; subst a; trivial
  · exact checked8412
theorem derived8412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8412 := by
  apply localUnsat_implies_entails f8412 [c8409, c8408, c1389, c1373, c8296, c1382, c1377, c1387, c1360, c8406, c1105, c8411, c1308, c1320, c1319, c1040, c1080, c2093, c1072, c1039, c1333, c2072, c1307, c2095] c8412 unsat8412 (by rfl) a
  have h0 : Entails.eval a c8409 := derived8409 a h
  have h1 : Entails.eval a c8408 := derived8408 a h
  have h2 : Entails.eval a c1389 := h 1388 (by decide)
  have h3 : Entails.eval a c1373 := h 1372 (by decide)
  have h4 : Entails.eval a c8296 := derived8296 a h
  have h5 : Entails.eval a c1382 := h 1381 (by decide)
  have h6 : Entails.eval a c1377 := h 1376 (by decide)
  have h7 : Entails.eval a c1387 := h 1386 (by decide)
  have h8 : Entails.eval a c1360 := h 1359 (by decide)
  have h9 : Entails.eval a c8406 := derived8406 a h
  have h10 : Entails.eval a c1105 := h 1104 (by decide)
  have h11 : Entails.eval a c8411 := derived8411 a h
  have h12 : Entails.eval a c1308 := h 1307 (by decide)
  have h13 : Entails.eval a c1320 := h 1319 (by decide)
  have h14 : Entails.eval a c1319 := h 1318 (by decide)
  have h15 : Entails.eval a c1040 := h 1039 (by decide)
  have h16 : Entails.eval a c1080 := h 1079 (by decide)
  have h17 : Entails.eval a c2093 := h 2092 (by decide)
  have h18 : Entails.eval a c1072 := h 1071 (by decide)
  have h19 : Entails.eval a c1039 := h 1038 (by decide)
  have h20 : Entails.eval a c1333 := h 1332 (by decide)
  have h21 : Entails.eval a c2072 := h 2071 (by decide)
  have h22 : Entails.eval a c1307 := h 1306 (by decide)
  have h23 : Entails.eval a c2095 := h 2094 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8413 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8407, some c8409, some c8408, some c8412, some c8385, some c1392, some c1387, some c8300, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8413 : lratChecker f8413 p8413 = .success := by decide +kernel
theorem unsat8413 : Unsatisfiable (PosFin 65) f8413 := by
  apply lratCheckerSound f8413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8413
  · intro a ha; simp [p8413] at ha; subst a; trivial
  · exact checked8413
theorem derived8413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8413 := by
  apply localUnsat_implies_entails f8413 [c8407, c8409, c8408, c8412, c8385, c1392, c1387, c8300] c8413 unsat8413 (by rfl) a
  have h0 : Entails.eval a c8407 := derived8407 a h
  have h1 : Entails.eval a c8409 := derived8409 a h
  have h2 : Entails.eval a c8408 := derived8408 a h
  have h3 : Entails.eval a c8412 := derived8412 a h
  have h4 : Entails.eval a c8385 := derived8385 a h
  have h5 : Entails.eval a c1392 := h 1391 (by decide)
  have h6 : Entails.eval a c1387 := h 1386 (by decide)
  have h7 : Entails.eval a c8300 := derived8300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8414 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1385, some c1394, some c1361, some c1379, some c2098, some c1267, some c1220, some c4619, some c4465, some c4305, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8414 : lratChecker f8414 p8414 = .success := by decide +kernel
theorem unsat8414 : Unsatisfiable (PosFin 65) f8414 := by
  apply lratCheckerSound f8414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8414
  · intro a ha; simp [p8414] at ha; subst a; trivial
  · exact checked8414
theorem derived8414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8414 := by
  apply localUnsat_implies_entails f8414 [c1385, c1394, c1361, c1379, c2098, c1267, c1220, c4619, c4465, c4305] c8414 unsat8414 (by rfl) a
  have h0 : Entails.eval a c1385 := h 1384 (by decide)
  have h1 : Entails.eval a c1394 := h 1393 (by decide)
  have h2 : Entails.eval a c1361 := h 1360 (by decide)
  have h3 : Entails.eval a c1379 := h 1378 (by decide)
  have h4 : Entails.eval a c2098 := h 2097 (by decide)
  have h5 : Entails.eval a c1267 := h 1266 (by decide)
  have h6 : Entails.eval a c1220 := h 1219 (by decide)
  have h7 : Entails.eval a c4619 := h 4618 (by decide)
  have h8 : Entails.eval a c4465 := h 4464 (by decide)
  have h9 : Entails.eval a c4305 := h 4304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8415 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨1, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8414, some c1386, some c1373, some c1375, some c1371, some c1377, some c1221, some c1284, some c4465, some c4733, some c4293, some c4290, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8415 : lratChecker f8415 p8415 = .success := by decide +kernel
theorem unsat8415 : Unsatisfiable (PosFin 65) f8415 := by
  apply lratCheckerSound f8415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8415
  · intro a ha; simp [p8415] at ha; subst a; trivial
  · exact checked8415
theorem derived8415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8415 := by
  apply localUnsat_implies_entails f8415 [c8414, c1386, c1373, c1375, c1371, c1377, c1221, c1284, c4465, c4733, c4293, c4290] c8415 unsat8415 (by rfl) a
  have h0 : Entails.eval a c8414 := derived8414 a h
  have h1 : Entails.eval a c1386 := h 1385 (by decide)
  have h2 : Entails.eval a c1373 := h 1372 (by decide)
  have h3 : Entails.eval a c1375 := h 1374 (by decide)
  have h4 : Entails.eval a c1371 := h 1370 (by decide)
  have h5 : Entails.eval a c1377 := h 1376 (by decide)
  have h6 : Entails.eval a c1221 := h 1220 (by decide)
  have h7 : Entails.eval a c1284 := h 1283 (by decide)
  have h8 : Entails.eval a c4465 := h 4464 (by decide)
  have h9 : Entails.eval a c4733 := h 4732 (by decide)
  have h10 : Entails.eval a c4293 := h 4292 (by decide)
  have h11 : Entails.eval a c4290 := h 4289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8416 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨56, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c1366, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8416 : lratChecker f8416 p8416 = .success := by decide +kernel
theorem unsat8416 : Unsatisfiable (PosFin 65) f8416 := by
  apply lratCheckerSound f8416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8416
  · intro a ha; simp [p8416] at ha; subst a; trivial
  · exact checked8416
theorem derived8416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8416 := by
  apply localUnsat_implies_entails f8416 [c8269, c1366] c8416 unsat8416 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c1366 := h 1365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8417 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8415, some c8385, some c8416, some c1384, some c1381, some c1385, some c1379, some c1283, some c1226, some c4734, some c4468, some c4308, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8417 : lratChecker f8417 p8417 = .success := by decide +kernel
theorem unsat8417 : Unsatisfiable (PosFin 65) f8417 := by
  apply lratCheckerSound f8417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8417
  · intro a ha; simp [p8417] at ha; subst a; trivial
  · exact checked8417
theorem derived8417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8417 := by
  apply localUnsat_implies_entails f8417 [c8415, c8385, c8416, c1384, c1381, c1385, c1379, c1283, c1226, c4734, c4468, c4308] c8417 unsat8417 (by rfl) a
  have h0 : Entails.eval a c8415 := derived8415 a h
  have h1 : Entails.eval a c8385 := derived8385 a h
  have h2 : Entails.eval a c8416 := derived8416 a h
  have h3 : Entails.eval a c1384 := h 1383 (by decide)
  have h4 : Entails.eval a c1381 := h 1380 (by decide)
  have h5 : Entails.eval a c1385 := h 1384 (by decide)
  have h6 : Entails.eval a c1379 := h 1378 (by decide)
  have h7 : Entails.eval a c1283 := h 1282 (by decide)
  have h8 : Entails.eval a c1226 := h 1225 (by decide)
  have h9 : Entails.eval a c4734 := h 4733 (by decide)
  have h10 : Entails.eval a c4468 := h 4467 (by decide)
  have h11 : Entails.eval a c4308 := h 4307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8418 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8415, some c8385, some c8416, some c8417, some c1387, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8418 : lratChecker f8418 p8418 = .success := by decide +kernel
theorem unsat8418 : Unsatisfiable (PosFin 65) f8418 := by
  apply lratCheckerSound f8418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8418
  · intro a ha; simp [p8418] at ha; subst a; trivial
  · exact checked8418
theorem derived8418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8418 := by
  apply localUnsat_implies_entails f8418 [c8415, c8385, c8416, c8417, c1387] c8418 unsat8418 (by rfl) a
  have h0 : Entails.eval a c8415 := derived8415 a h
  have h1 : Entails.eval a c8385 := derived8385 a h
  have h2 : Entails.eval a c8416 := derived8416 a h
  have h3 : Entails.eval a c8417 := derived8417 a h
  have h4 : Entails.eval a c1387 := h 1386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8419 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8409, some c8408, some c1389, some c1373, some c1397, some c1382, some c1377, some c1387, some c1360, some c2108, some c8406, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8419 : lratChecker f8419 p8419 = .success := by decide +kernel
theorem unsat8419 : Unsatisfiable (PosFin 65) f8419 := by
  apply lratCheckerSound f8419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8419
  · intro a ha; simp [p8419] at ha; subst a; trivial
  · exact checked8419
theorem derived8419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8419 := by
  apply localUnsat_implies_entails f8419 [c8409, c8408, c1389, c1373, c1397, c1382, c1377, c1387, c1360, c2108, c8406] c8419 unsat8419 (by rfl) a
  have h0 : Entails.eval a c8409 := derived8409 a h
  have h1 : Entails.eval a c8408 := derived8408 a h
  have h2 : Entails.eval a c1389 := h 1388 (by decide)
  have h3 : Entails.eval a c1373 := h 1372 (by decide)
  have h4 : Entails.eval a c1397 := h 1396 (by decide)
  have h5 : Entails.eval a c1382 := h 1381 (by decide)
  have h6 : Entails.eval a c1377 := h 1376 (by decide)
  have h7 : Entails.eval a c1387 := h 1386 (by decide)
  have h8 : Entails.eval a c1360 := h 1359 (by decide)
  have h9 : Entails.eval a c2108 := h 2107 (by decide)
  have h10 : Entails.eval a c8406 := derived8406 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8420 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8418, some c8409, some c8408, some c8419, some c8385, some c8416, some c1387, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8420 : lratChecker f8420 p8420 = .success := by decide +kernel
theorem unsat8420 : Unsatisfiable (PosFin 65) f8420 := by
  apply lratCheckerSound f8420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8420
  · intro a ha; simp [p8420] at ha; subst a; trivial
  · exact checked8420
theorem derived8420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8420 := by
  apply localUnsat_implies_entails f8420 [c8418, c8409, c8408, c8419, c8385, c8416, c1387] c8420 unsat8420 (by rfl) a
  have h0 : Entails.eval a c8418 := derived8418 a h
  have h1 : Entails.eval a c8409 := derived8409 a h
  have h2 : Entails.eval a c8408 := derived8408 a h
  have h3 : Entails.eval a c8419 := derived8419 a h
  have h4 : Entails.eval a c8385 := derived8385 a h
  have h5 : Entails.eval a c8416 := derived8416 a h
  have h6 : Entails.eval a c1387 := h 1386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8421 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8413, some c8420, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8421 : lratChecker f8421 p8421 = .success := by decide +kernel
theorem unsat8421 : Unsatisfiable (PosFin 65) f8421 := by
  apply lratCheckerSound f8421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8421
  · intro a ha; simp [p8421] at ha; subst a; trivial
  · exact checked8421
theorem derived8421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8421 := by
  apply localUnsat_implies_entails f8421 [c8413, c8420] c8421 unsat8421 (by rfl) a
  have h0 : Entails.eval a c8413 := derived8413 a h
  have h1 : Entails.eval a c8420 := derived8420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8422 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨59, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5892, some c5901, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p8422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8422 : lratChecker f8422 p8422 = .success := by decide +kernel
theorem unsat8422 : Unsatisfiable (PosFin 65) f8422 := by
  apply lratCheckerSound f8422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8422
  · intro a ha; simp [p8422] at ha; subst a; trivial
  · exact checked8422
theorem derived8422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8422 := by
  apply localUnsat_implies_entails f8422 [c5892, c5901] c8422 unsat8422 (by rfl) a
  have h0 : Entails.eval a c5892 := h 5891 (by decide)
  have h1 : Entails.eval a c5901 := h 5900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8423 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨59, by decide⟩, true), (⟨18, by decide⟩, true), (⟨51, by decide⟩, true), (⟨19, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c653, some c654, some c689, some c704, some c670, some c669, some c690, some c702, some c681, some c705, some c8422, some c5580, some c6025, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8423 : lratChecker f8423 p8423 = .success := by decide +kernel
theorem unsat8423 : Unsatisfiable (PosFin 65) f8423 := by
  apply lratCheckerSound f8423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8423
  · intro a ha; simp [p8423] at ha; subst a; trivial
  · exact checked8423
theorem derived8423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8423 := by
  apply localUnsat_implies_entails f8423 [c8380, c653, c654, c689, c704, c670, c669, c690, c702, c681, c705, c8422, c5580, c6025] c8423 unsat8423 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c653 := h 652 (by decide)
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c689 := h 688 (by decide)
  have h4 : Entails.eval a c704 := h 703 (by decide)
  have h5 : Entails.eval a c670 := h 669 (by decide)
  have h6 : Entails.eval a c669 := h 668 (by decide)
  have h7 : Entails.eval a c690 := h 689 (by decide)
  have h8 : Entails.eval a c702 := h 701 (by decide)
  have h9 : Entails.eval a c681 := h 680 (by decide)
  have h10 : Entails.eval a c705 := h 704 (by decide)
  have h11 : Entails.eval a c8422 := derived8422 a h
  have h12 : Entails.eval a c5580 := h 5579 (by decide)
  have h13 : Entails.eval a c6025 := h 6024 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8424 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5511, some c5552, some c5542, some c5943, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8424 : lratChecker f8424 p8424 = .success := by decide +kernel
theorem unsat8424 : Unsatisfiable (PosFin 65) f8424 := by
  apply lratCheckerSound f8424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8424
  · intro a ha; simp [p8424] at ha; subst a; trivial
  · exact checked8424
theorem derived8424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8424 := by
  apply localUnsat_implies_entails f8424 [c5511, c5552, c5542, c5943] c8424 unsat8424 (by rfl) a
  have h0 : Entails.eval a c5511 := h 5510 (by decide)
  have h1 : Entails.eval a c5552 := h 5551 (by decide)
  have h2 : Entails.eval a c5542 := h 5541 (by decide)
  have h3 : Entails.eval a c5943 := h 5942 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8425 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨51, by decide⟩, true), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8424, some c653, some c654, some c8423, some c5949, some c5517, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8425 : lratChecker f8425 p8425 = .success := by decide +kernel
theorem unsat8425 : Unsatisfiable (PosFin 65) f8425 := by
  apply lratCheckerSound f8425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8425
  · intro a ha; simp [p8425] at ha; subst a; trivial
  · exact checked8425
theorem derived8425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8425 := by
  apply localUnsat_implies_entails f8425 [c8380, c8424, c653, c654, c8423, c5949, c5517] c8425 unsat8425 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8424 := derived8424 a h
  have h2 : Entails.eval a c653 := h 652 (by decide)
  have h3 : Entails.eval a c654 := h 653 (by decide)
  have h4 : Entails.eval a c8423 := derived8423 a h
  have h5 : Entails.eval a c5949 := h 5948 (by decide)
  have h6 : Entails.eval a c5517 := h 5516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8426 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c672, some c673, some c669, some c688, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8426 : lratChecker f8426 p8426 = .success := by decide +kernel
theorem unsat8426 : Unsatisfiable (PosFin 65) f8426 := by
  apply lratCheckerSound f8426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8426
  · intro a ha; simp [p8426] at ha; subst a; trivial
  · exact checked8426
theorem derived8426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8426 := by
  apply localUnsat_implies_entails f8426 [c672, c673, c669, c688] c8426 unsat8426 (by rfl) a
  have h0 : Entails.eval a c672 := h 671 (by decide)
  have h1 : Entails.eval a c673 := h 672 (by decide)
  have h2 : Entails.eval a c669 := h 668 (by decide)
  have h3 : Entails.eval a c688 := h 687 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8427 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨24, by decide⟩, false), (⟨49, by decide⟩, false), (⟨59, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c701, some c681, some c6081, some c6079, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8427 : lratChecker f8427 p8427 = .success := by decide +kernel
theorem unsat8427 : Unsatisfiable (PosFin 65) f8427 := by
  apply lratCheckerSound f8427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8427
  · intro a ha; simp [p8427] at ha; subst a; trivial
  · exact checked8427
theorem derived8427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8427 := by
  apply localUnsat_implies_entails f8427 [c701, c681, c6081, c6079] c8427 unsat8427 (by rfl) a
  have h0 : Entails.eval a c701 := h 700 (by decide)
  have h1 : Entails.eval a c681 := h 680 (by decide)
  have h2 : Entails.eval a c6081 := h 6080 (by decide)
  have h3 : Entails.eval a c6079 := h 6078 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8428 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨59, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8426, some c662, some c8427, some c678, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8428 : lratChecker f8428 p8428 = .success := by decide +kernel
theorem unsat8428 : Unsatisfiable (PosFin 65) f8428 := by
  apply lratCheckerSound f8428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8428
  · intro a ha; simp [p8428] at ha; subst a; trivial
  · exact checked8428
theorem derived8428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8428 := by
  apply localUnsat_implies_entails f8428 [c8426, c662, c8427, c678] c8428 unsat8428 (by rfl) a
  have h0 : Entails.eval a c8426 := derived8426 a h
  have h1 : Entails.eval a c662 := h 661 (by decide)
  have h2 : Entails.eval a c8427 := derived8427 a h
  have h3 : Entails.eval a c678 := h 677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8429 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5701, some c5750, some c5888, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p8429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8429 : lratChecker f8429 p8429 = .success := by decide +kernel
theorem unsat8429 : Unsatisfiable (PosFin 65) f8429 := by
  apply lratCheckerSound f8429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8429
  · intro a ha; simp [p8429] at ha; subst a; trivial
  · exact checked8429
theorem derived8429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8429 := by
  apply localUnsat_implies_entails f8429 [c5701, c5750, c5888] c8429 unsat8429 (by rfl) a
  have h0 : Entails.eval a c5701 := h 5700 (by decide)
  have h1 : Entails.eval a c5750 := h 5749 (by decide)
  have h2 : Entails.eval a c5888 := h 5887 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8430 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8429, some c5620, some c6101, some c212, some c6032, some c1262, some c1197, some c4442, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8430 : lratChecker f8430 p8430 = .success := by decide +kernel
theorem unsat8430 : Unsatisfiable (PosFin 65) f8430 := by
  apply lratCheckerSound f8430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8430
  · intro a ha; simp [p8430] at ha; subst a; trivial
  · exact checked8430
theorem derived8430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8430 := by
  apply localUnsat_implies_entails f8430 [c8429, c5620, c6101, c212, c6032, c1262, c1197, c4442] c8430 unsat8430 (by rfl) a
  have h0 : Entails.eval a c8429 := derived8429 a h
  have h1 : Entails.eval a c5620 := h 5619 (by decide)
  have h2 : Entails.eval a c6101 := h 6100 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c6032 := h 6031 (by decide)
  have h5 : Entails.eval a c1262 := h 1261 (by decide)
  have h6 : Entails.eval a c1197 := h 1196 (by decide)
  have h7 : Entails.eval a c4442 := h 4441 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8431 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8430, some c5812, some c5783, some c5650, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p8431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8431 : lratChecker f8431 p8431 = .success := by decide +kernel
theorem unsat8431 : Unsatisfiable (PosFin 65) f8431 := by
  apply lratCheckerSound f8431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8431
  · intro a ha; simp [p8431] at ha; subst a; trivial
  · exact checked8431
theorem derived8431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8431 := by
  apply localUnsat_implies_entails f8431 [c8430, c5812, c5783, c5650] c8431 unsat8431 (by rfl) a
  have h0 : Entails.eval a c8430 := derived8430 a h
  have h1 : Entails.eval a c5812 := h 5811 (by decide)
  have h2 : Entails.eval a c5783 := h 5782 (by decide)
  have h3 : Entails.eval a c5650 := h 5649 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8432 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨19, by decide⟩, true), (⟨63, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8431, some c8426, some c8428, some c661, some c5645, some c6121, some c674, some c5810, some c689, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8432 : lratChecker f8432 p8432 = .success := by decide +kernel
theorem unsat8432 : Unsatisfiable (PosFin 65) f8432 := by
  apply lratCheckerSound f8432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8432
  · intro a ha; simp [p8432] at ha; subst a; trivial
  · exact checked8432
theorem derived8432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8432 := by
  apply localUnsat_implies_entails f8432 [c8380, c8431, c8426, c8428, c661, c5645, c6121, c674, c5810, c689] c8432 unsat8432 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8431 := derived8431 a h
  have h2 : Entails.eval a c8426 := derived8426 a h
  have h3 : Entails.eval a c8428 := derived8428 a h
  have h4 : Entails.eval a c661 := h 660 (by decide)
  have h5 : Entails.eval a c5645 := h 5644 (by decide)
  have h6 : Entails.eval a c6121 := h 6120 (by decide)
  have h7 : Entails.eval a c674 := h 673 (by decide)
  have h8 : Entails.eval a c5810 := h 5809 (by decide)
  have h9 : Entails.eval a c689 := h 688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8433 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8432, some c8424, some c8425, some c653, some c654, some c628, some c689, some c5710, some c5536, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8433 : lratChecker f8433 p8433 = .success := by decide +kernel
theorem unsat8433 : Unsatisfiable (PosFin 65) f8433 := by
  apply lratCheckerSound f8433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8433
  · intro a ha; simp [p8433] at ha; subst a; trivial
  · exact checked8433
theorem derived8433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8433 := by
  apply localUnsat_implies_entails f8433 [c8380, c8432, c8424, c8425, c653, c654, c628, c689, c5710, c5536] c8433 unsat8433 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8432 := derived8432 a h
  have h2 : Entails.eval a c8424 := derived8424 a h
  have h3 : Entails.eval a c8425 := derived8425 a h
  have h4 : Entails.eval a c653 := h 652 (by decide)
  have h5 : Entails.eval a c654 := h 653 (by decide)
  have h6 : Entails.eval a c628 := h 627 (by decide)
  have h7 : Entails.eval a c689 := h 688 (by decide)
  have h8 : Entails.eval a c5710 := h 5709 (by decide)
  have h9 : Entails.eval a c5536 := h 5535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8434 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, true), (⟨59, by decide⟩, true), (⟨29, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c690, some c692, some c675, some c667, some c703, some c698, some c8422, some c5580, some c5863, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8434 : lratChecker f8434 p8434 = .success := by decide +kernel
theorem unsat8434 : Unsatisfiable (PosFin 65) f8434 := by
  apply lratCheckerSound f8434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8434
  · intro a ha; simp [p8434] at ha; subst a; trivial
  · exact checked8434
theorem derived8434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8434 := by
  apply localUnsat_implies_entails f8434 [c8380, c690, c692, c675, c667, c703, c698, c8422, c5580, c5863] c8434 unsat8434 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c690 := h 689 (by decide)
  have h2 : Entails.eval a c692 := h 691 (by decide)
  have h3 : Entails.eval a c675 := h 674 (by decide)
  have h4 : Entails.eval a c667 := h 666 (by decide)
  have h5 : Entails.eval a c703 := h 702 (by decide)
  have h6 : Entails.eval a c698 := h 697 (by decide)
  have h7 : Entails.eval a c8422 := derived8422 a h
  have h8 : Entails.eval a c5580 := h 5579 (by decide)
  have h9 : Entails.eval a c5863 := h 5862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8435 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c707, some c701, some c704, some c700, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8435 : lratChecker f8435 p8435 = .success := by decide +kernel
theorem unsat8435 : Unsatisfiable (PosFin 65) f8435 := by
  apply lratCheckerSound f8435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8435
  · intro a ha; simp [p8435] at ha; subst a; trivial
  · exact checked8435
theorem derived8435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8435 := by
  apply localUnsat_implies_entails f8435 [c707, c701, c704, c700] c8435 unsat8435 (by rfl) a
  have h0 : Entails.eval a c707 := h 706 (by decide)
  have h1 : Entails.eval a c701 := h 700 (by decide)
  have h2 : Entails.eval a c704 := h 703 (by decide)
  have h3 : Entails.eval a c700 := h 699 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8436 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c689, some c679, some c656, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8436 : lratChecker f8436 p8436 = .success := by decide +kernel
theorem unsat8436 : Unsatisfiable (PosFin 65) f8436 := by
  apply lratCheckerSound f8436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8436
  · intro a ha; simp [p8436] at ha; subst a; trivial
  · exact checked8436
theorem derived8436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8436 := by
  apply localUnsat_implies_entails f8436 [c689, c679, c656] c8436 unsat8436 (by rfl) a
  have h0 : Entails.eval a c689 := h 688 (by decide)
  have h1 : Entails.eval a c679 := h 678 (by decide)
  have h2 : Entails.eval a c656 := h 655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8437 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8436, some c8434, some c690, some c5856, some c5973, some c5983, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8437 : lratChecker f8437 p8437 = .success := by decide +kernel
theorem unsat8437 : Unsatisfiable (PosFin 65) f8437 := by
  apply lratCheckerSound f8437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8437
  · intro a ha; simp [p8437] at ha; subst a; trivial
  · exact checked8437
theorem derived8437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8437 := by
  apply localUnsat_implies_entails f8437 [c8435, c8436, c8434, c690, c5856, c5973, c5983] c8437 unsat8437 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8436 := derived8436 a h
  have h2 : Entails.eval a c8434 := derived8434 a h
  have h3 : Entails.eval a c690 := h 689 (by decide)
  have h4 : Entails.eval a c5856 := h 5855 (by decide)
  have h5 : Entails.eval a c5973 := h 5972 (by decide)
  have h6 : Entails.eval a c5983 := h 5982 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8438 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c660, some c665, some c671, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8438 : lratChecker f8438 p8438 = .success := by decide +kernel
theorem unsat8438 : Unsatisfiable (PosFin 65) f8438 := by
  apply lratCheckerSound f8438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8438
  · intro a ha; simp [p8438] at ha; subst a; trivial
  · exact checked8438
theorem derived8438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8438 := by
  apply localUnsat_implies_entails f8438 [c660, c665, c671] c8438 unsat8438 (by rfl) a
  have h0 : Entails.eval a c660 := h 659 (by decide)
  have h1 : Entails.eval a c665 := h 664 (by decide)
  have h2 : Entails.eval a c671 := h 670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8439 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8438, some c8435, some c8436, some c8437, some c6124, some c5859, some c6112, some c5987, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8439 : lratChecker f8439 p8439 = .success := by decide +kernel
theorem unsat8439 : Unsatisfiable (PosFin 65) f8439 := by
  apply lratCheckerSound f8439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8439
  · intro a ha; simp [p8439] at ha; subst a; trivial
  · exact checked8439
theorem derived8439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8439 := by
  apply localUnsat_implies_entails f8439 [c8438, c8435, c8436, c8437, c6124, c5859, c6112, c5987] c8439 unsat8439 (by rfl) a
  have h0 : Entails.eval a c8438 := derived8438 a h
  have h1 : Entails.eval a c8435 := derived8435 a h
  have h2 : Entails.eval a c8436 := derived8436 a h
  have h3 : Entails.eval a c8437 := derived8437 a h
  have h4 : Entails.eval a c6124 := h 6123 (by decide)
  have h5 : Entails.eval a c5859 := h 5858 (by decide)
  have h6 : Entails.eval a c6112 := h 6111 (by decide)
  have h7 : Entails.eval a c5987 := h 5986 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8440 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨22, by decide⟩, true), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5943, some c6237, some c5862, some c5863, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p8440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8440 : lratChecker f8440 p8440 = .success := by decide +kernel
theorem unsat8440 : Unsatisfiable (PosFin 65) f8440 := by
  apply lratCheckerSound f8440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8440
  · intro a ha; simp [p8440] at ha; subst a; trivial
  · exact checked8440
theorem derived8440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8440 := by
  apply localUnsat_implies_entails f8440 [c5943, c6237, c5862, c5863] c8440 unsat8440 (by rfl) a
  have h0 : Entails.eval a c5943 := h 5942 (by decide)
  have h1 : Entails.eval a c6237 := h 6236 (by decide)
  have h2 : Entails.eval a c5862 := h 5861 (by decide)
  have h3 : Entails.eval a c5863 := h 5862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8441 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨49, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5662, some c5603, some c5740, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p8441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8441 : lratChecker f8441 p8441 = .success := by decide +kernel
theorem unsat8441 : Unsatisfiable (PosFin 65) f8441 := by
  apply lratCheckerSound f8441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8441
  · intro a ha; simp [p8441] at ha; subst a; trivial
  · exact checked8441
theorem derived8441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8441 := by
  apply localUnsat_implies_entails f8441 [c5662, c5603, c5740] c8441 unsat8441 (by rfl) a
  have h0 : Entails.eval a c5662 := h 5661 (by decide)
  have h1 : Entails.eval a c5603 := h 5602 (by decide)
  have h2 : Entails.eval a c5740 := h 5739 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8442 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨26, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6101, some c8440, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p8442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8442 : lratChecker f8442 p8442 = .success := by decide +kernel
theorem unsat8442 : Unsatisfiable (PosFin 65) f8442 := by
  apply lratCheckerSound f8442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8442
  · intro a ha; simp [p8442] at ha; subst a; trivial
  · exact checked8442
theorem derived8442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8442 := by
  apply localUnsat_implies_entails f8442 [c6101, c8440] c8442 unsat8442 (by rfl) a
  have h0 : Entails.eval a c6101 := h 6100 (by decide)
  have h1 : Entails.eval a c8440 := derived8440 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8443 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8380, some c8439, some c8441, some c8442, some c5636, some c5682, some c5763, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8443 : lratChecker f8443 p8443 = .success := by decide +kernel
theorem unsat8443 : Unsatisfiable (PosFin 65) f8443 := by
  apply lratCheckerSound f8443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8443
  · intro a ha; simp [p8443] at ha; subst a; trivial
  · exact checked8443
theorem derived8443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8443 := by
  apply localUnsat_implies_entails f8443 [c8380, c8439, c8441, c8442, c5636, c5682, c5763] c8443 unsat8443 (by rfl) a
  have h0 : Entails.eval a c8380 := derived8380 a h
  have h1 : Entails.eval a c8439 := derived8439 a h
  have h2 : Entails.eval a c8441 := derived8441 a h
  have h3 : Entails.eval a c8442 := derived8442 a h
  have h4 : Entails.eval a c5636 := h 5635 (by decide)
  have h5 : Entails.eval a c5682 := h 5681 (by decide)
  have h6 : Entails.eval a c5763 := h 5762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8444 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨51, by decide⟩, true), (⟨28, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c690, some c692, some c675, some c703, some c662, some c6183, some c6188, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8444 : lratChecker f8444 p8444 = .success := by decide +kernel
theorem unsat8444 : Unsatisfiable (PosFin 65) f8444 := by
  apply lratCheckerSound f8444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8444
  · intro a ha; simp [p8444] at ha; subst a; trivial
  · exact checked8444
theorem derived8444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8444 := by
  apply localUnsat_implies_entails f8444 [c690, c692, c675, c703, c662, c6183, c6188] c8444 unsat8444 (by rfl) a
  have h0 : Entails.eval a c690 := h 689 (by decide)
  have h1 : Entails.eval a c692 := h 691 (by decide)
  have h2 : Entails.eval a c675 := h 674 (by decide)
  have h3 : Entails.eval a c703 := h 702 (by decide)
  have h4 : Entails.eval a c662 := h 661 (by decide)
  have h5 : Entails.eval a c6183 := h 6182 (by decide)
  have h6 : Entails.eval a c6188 := h 6187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8445 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c689, some c693, some c679, some c682, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p8445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8445 : lratChecker f8445 p8445 = .success := by decide +kernel
theorem unsat8445 : Unsatisfiable (PosFin 65) f8445 := by
  apply lratCheckerSound f8445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8445
  · intro a ha; simp [p8445] at ha; subst a; trivial
  · exact checked8445
theorem derived8445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8445 := by
  apply localUnsat_implies_entails f8445 [c689, c693, c679, c682] c8445 unsat8445 (by rfl) a
  have h0 : Entails.eval a c689 := h 688 (by decide)
  have h1 : Entails.eval a c693 := h 692 (by decide)
  have h2 : Entails.eval a c679 := h 678 (by decide)
  have h3 : Entails.eval a c682 := h 681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8446 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8435, some c8445, some c690, some c8444, some c5979, some c5859, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8446 : lratChecker f8446 p8446 = .success := by decide +kernel
theorem unsat8446 : Unsatisfiable (PosFin 65) f8446 := by
  apply lratCheckerSound f8446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8446
  · intro a ha; simp [p8446] at ha; subst a; trivial
  · exact checked8446
theorem derived8446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8446 := by
  apply localUnsat_implies_entails f8446 [c8435, c8445, c690, c8444, c5979, c5859] c8446 unsat8446 (by rfl) a
  have h0 : Entails.eval a c8435 := derived8435 a h
  have h1 : Entails.eval a c8445 := derived8445 a h
  have h2 : Entails.eval a c690 := h 689 (by decide)
  have h3 : Entails.eval a c8444 := derived8444 a h
  have h4 : Entails.eval a c5979 := h 5978 (by decide)
  have h5 : Entails.eval a c5859 := h 5858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8447 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1241, some c1304, some c4741, some c5322, some c5342, some c292, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8447 : lratChecker f8447 p8447 = .success := by decide +kernel
theorem unsat8447 : Unsatisfiable (PosFin 65) f8447 := by
  apply lratCheckerSound f8447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8447
  · intro a ha; simp [p8447] at ha; subst a; trivial
  · exact checked8447
theorem derived8447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8447 := by
  apply localUnsat_implies_entails f8447 [c1241, c1304, c4741, c5322, c5342, c292] c8447 unsat8447 (by rfl) a
  have h0 : Entails.eval a c1241 := h 1240 (by decide)
  have h1 : Entails.eval a c1304 := h 1303 (by decide)
  have h2 : Entails.eval a c4741 := h 4740 (by decide)
  have h3 : Entails.eval a c5322 := h 5321 (by decide)
  have h4 : Entails.eval a c5342 := h 5341 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8448 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨24, by decide⟩, true), (⟨51, by decide⟩, true), (⟨22, by decide⟩, true), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8447, some c5370, some c180, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8448 : lratChecker f8448 p8448 = .success := by decide +kernel
theorem unsat8448 : Unsatisfiable (PosFin 65) f8448 := by
  apply lratCheckerSound f8448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8448
  · intro a ha; simp [p8448] at ha; subst a; trivial
  · exact checked8448
theorem derived8448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8448 := by
  apply localUnsat_implies_entails f8448 [c8447, c5370, c180] c8448 unsat8448 (by rfl) a
  have h0 : Entails.eval a c8447 := derived8447 a h
  have h1 : Entails.eval a c5370 := h 5369 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8449 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨22, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8444, some c676, some c677, some c661, some c691, some c667, some c8448, some c6016, some c5866, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8449 : lratChecker f8449 p8449 = .success := by decide +kernel
theorem unsat8449 : Unsatisfiable (PosFin 65) f8449 := by
  apply lratCheckerSound f8449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8449
  · intro a ha; simp [p8449] at ha; subst a; trivial
  · exact checked8449
theorem derived8449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8449 := by
  apply localUnsat_implies_entails f8449 [c8444, c676, c677, c661, c691, c667, c8448, c6016, c5866] c8449 unsat8449 (by rfl) a
  have h0 : Entails.eval a c8444 := derived8444 a h
  have h1 : Entails.eval a c676 := h 675 (by decide)
  have h2 : Entails.eval a c677 := h 676 (by decide)
  have h3 : Entails.eval a c661 := h 660 (by decide)
  have h4 : Entails.eval a c691 := h 690 (by decide)
  have h5 : Entails.eval a c667 := h 666 (by decide)
  have h6 : Entails.eval a c8448 := derived8448 a h
  have h7 : Entails.eval a c6016 := h 6015 (by decide)
  have h8 : Entails.eval a c5866 := h 5865 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8450 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨62, by decide⟩, false), (⟨50, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8421, some c8449, some c1434, some c125, some c4911, some c5375, some c224, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8450 : lratChecker f8450 p8450 = .success := by decide +kernel
theorem unsat8450 : Unsatisfiable (PosFin 65) f8450 := by
  apply lratCheckerSound f8450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8450
  · intro a ha; simp [p8450] at ha; subst a; trivial
  · exact checked8450
theorem derived8450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8450 := by
  apply localUnsat_implies_entails f8450 [c8421, c8449, c1434, c125, c4911, c5375, c224] c8450 unsat8450 (by rfl) a
  have h0 : Entails.eval a c8421 := derived8421 a h
  have h1 : Entails.eval a c8449 := derived8449 a h
  have h2 : Entails.eval a c1434 := h 1433 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c4911 := h 4910 (by decide)
  have h5 : Entails.eval a c5375 := h 5374 (by decide)
  have h6 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8450

end CochromaticTwenty.Certificates.FixedCore0
