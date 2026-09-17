import MerLeanExperiment.Certificates.FixedCore0.Inputs

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7551 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5796, some c6243, some c5807, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p7551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7551 : lratChecker f7551 p7551 = .success := by decide +kernel
theorem unsat7551 : Unsatisfiable (PosFin 65) f7551 := by
  apply lratCheckerSound f7551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7551
  · intro a ha; simp [p7551] at ha; subst a; trivial
  · exact checked7551
theorem derived7551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7551 := by
  apply localUnsat_implies_entails f7551 [c5796, c6243, c5807] c7551 unsat7551 (by rfl) a
  have h0 : Entails.eval a c5796 := h 5795 (by decide)
  have h1 : Entails.eval a c6243 := h 6242 (by decide)
  have h2 : Entails.eval a c5807 := h 5806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7552 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6368, some c6402, some c6384, some c7443, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7552 : lratChecker f7552 p7552 = .success := by decide +kernel
theorem unsat7552 : Unsatisfiable (PosFin 65) f7552 := by
  apply lratCheckerSound f7552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7552
  · intro a ha; simp [p7552] at ha; subst a; trivial
  · exact checked7552
theorem derived7552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7552 := by
  apply localUnsat_implies_entails f7552 [c6368, c6402, c6384, c7443] c7552 unsat7552 (by rfl) a
  have h0 : Entails.eval a c6368 := h 6367 (by decide)
  have h1 : Entails.eval a c6402 := h 6401 (by decide)
  have h2 : Entails.eval a c6384 := h 6383 (by decide)
  have h3 : Entails.eval a c7443 := h 7442 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7553 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, true), (⟨55, by decide⟩, false), (⟨58, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6837, some c6849, some c7056, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7553 : lratChecker f7553 p7553 = .success := by decide +kernel
theorem unsat7553 : Unsatisfiable (PosFin 65) f7553 := by
  apply lratCheckerSound f7553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7553
  · intro a ha; simp [p7553] at ha; subst a; trivial
  · exact checked7553
theorem derived7553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7553 := by
  apply localUnsat_implies_entails f7553 [c6837, c6849, c7056] c7553 unsat7553 (by rfl) a
  have h0 : Entails.eval a c6837 := h 6836 (by decide)
  have h1 : Entails.eval a c6849 := h 6848 (by decide)
  have h2 : Entails.eval a c7056 := h 7055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7554 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨56, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5216, some c5194, some c5255, some c5720, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7554 : lratChecker f7554 p7554 = .success := by decide +kernel
theorem unsat7554 : Unsatisfiable (PosFin 65) f7554 := by
  apply lratCheckerSound f7554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7554
  · intro a ha; simp [p7554] at ha; subst a; trivial
  · exact checked7554
theorem derived7554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7554 := by
  apply localUnsat_implies_entails f7554 [c5216, c5194, c5255, c5720] c7554 unsat7554 (by rfl) a
  have h0 : Entails.eval a c5216 := h 5215 (by decide)
  have h1 : Entails.eval a c5194 := h 5193 (by decide)
  have h2 : Entails.eval a c5255 := h 5254 (by decide)
  have h3 : Entails.eval a c5720 := h 5719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7555 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨56, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5539, some c5720, some c5169, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7555 : lratChecker f7555 p7555 = .success := by decide +kernel
theorem unsat7555 : Unsatisfiable (PosFin 65) f7555 := by
  apply lratCheckerSound f7555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7555
  · intro a ha; simp [p7555] at ha; subst a; trivial
  · exact checked7555
theorem derived7555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7555 := by
  apply localUnsat_implies_entails f7555 [c5539, c5720, c5169] c7555 unsat7555 (by rfl) a
  have h0 : Entails.eval a c5539 := h 5538 (by decide)
  have h1 : Entails.eval a c5720 := h 5719 (by decide)
  have h2 : Entails.eval a c5169 := h 5168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7556 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨56, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5185, some c5150, some c5341, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7556 : lratChecker f7556 p7556 = .success := by decide +kernel
theorem unsat7556 : Unsatisfiable (PosFin 65) f7556 := by
  apply lratCheckerSound f7556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7556
  · intro a ha; simp [p7556] at ha; subst a; trivial
  · exact checked7556
theorem derived7556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7556 := by
  apply localUnsat_implies_entails f7556 [c5185, c5150, c5341] c7556 unsat7556 (by rfl) a
  have h0 : Entails.eval a c5185 := h 5184 (by decide)
  have h1 : Entails.eval a c5150 := h 5149 (by decide)
  have h2 : Entails.eval a c5341 := h 5340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7557 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨36, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6810, some c6823, some c7335, some c6738, some c7117, some c6666, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7557 : lratChecker f7557 p7557 = .success := by decide +kernel
theorem unsat7557 : Unsatisfiable (PosFin 65) f7557 := by
  apply lratCheckerSound f7557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7557
  · intro a ha; simp [p7557] at ha; subst a; trivial
  · exact checked7557
theorem derived7557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7557 := by
  apply localUnsat_implies_entails f7557 [c6810, c6823, c7335, c6738, c7117, c6666] c7557 unsat7557 (by rfl) a
  have h0 : Entails.eval a c6810 := h 6809 (by decide)
  have h1 : Entails.eval a c6823 := h 6822 (by decide)
  have h2 : Entails.eval a c7335 := h 7334 (by decide)
  have h3 : Entails.eval a c6738 := h 6737 (by decide)
  have h4 : Entails.eval a c7117 := h 7116 (by decide)
  have h5 : Entails.eval a c6666 := h 6665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7558 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨36, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7557, some c6777, some c6795, some c7128, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7558 : lratChecker f7558 p7558 = .success := by decide +kernel
theorem unsat7558 : Unsatisfiable (PosFin 65) f7558 := by
  apply lratCheckerSound f7558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7558
  · intro a ha; simp [p7558] at ha; subst a; trivial
  · exact checked7558
theorem derived7558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7558 := by
  apply localUnsat_implies_entails f7558 [c7557, c6777, c6795, c7128] c7558 unsat7558 (by rfl) a
  have h0 : Entails.eval a c7557 := derived7557 a h
  have h1 : Entails.eval a c6777 := h 6776 (by decide)
  have h2 : Entails.eval a c6795 := h 6794 (by decide)
  have h3 : Entails.eval a c7128 := h 7127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7559 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨57, by decide⟩, false), (⟨64, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7558, some c7552, some c6612, some c6969, some c6296, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7559 : lratChecker f7559 p7559 = .success := by decide +kernel
theorem unsat7559 : Unsatisfiable (PosFin 65) f7559 := by
  apply lratCheckerSound f7559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7559
  · intro a ha; simp [p7559] at ha; subst a; trivial
  · exact checked7559
theorem derived7559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7559 := by
  apply localUnsat_implies_entails f7559 [c7558, c7552, c6612, c6969, c6296] c7559 unsat7559 (by rfl) a
  have h0 : Entails.eval a c7558 := derived7558 a h
  have h1 : Entails.eval a c7552 := derived7552 a h
  have h2 : Entails.eval a c6612 := h 6611 (by decide)
  have h3 : Entails.eval a c6969 := h 6968 (by decide)
  have h4 : Entails.eval a c6296 := h 6295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7560 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7559, some c7552, some c6340, some c7224, some c7240, some c6640, some c6765, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7560 : lratChecker f7560 p7560 = .success := by decide +kernel
theorem unsat7560 : Unsatisfiable (PosFin 65) f7560 := by
  apply lratCheckerSound f7560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7560
  · intro a ha; simp [p7560] at ha; subst a; trivial
  · exact checked7560
theorem derived7560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7560 := by
  apply localUnsat_implies_entails f7560 [c7559, c7552, c6340, c7224, c7240, c6640, c6765] c7560 unsat7560 (by rfl) a
  have h0 : Entails.eval a c7559 := derived7559 a h
  have h1 : Entails.eval a c7552 := derived7552 a h
  have h2 : Entails.eval a c6340 := h 6339 (by decide)
  have h3 : Entails.eval a c7224 := h 7223 (by decide)
  have h4 : Entails.eval a c7240 := h 7239 (by decide)
  have h5 : Entails.eval a c6640 := h 6639 (by decide)
  have h6 : Entails.eval a c6765 := h 6764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7561 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5217, some c5229, some c5163, some c5423, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7561 : lratChecker f7561 p7561 = .success := by decide +kernel
theorem unsat7561 : Unsatisfiable (PosFin 65) f7561 := by
  apply lratCheckerSound f7561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7561
  · intro a ha; simp [p7561] at ha; subst a; trivial
  · exact checked7561
theorem derived7561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7561 := by
  apply localUnsat_implies_entails f7561 [c5217, c5229, c5163, c5423] c7561 unsat7561 (by rfl) a
  have h0 : Entails.eval a c5217 := h 5216 (by decide)
  have h1 : Entails.eval a c5229 := h 5228 (by decide)
  have h2 : Entails.eval a c5163 := h 5162 (by decide)
  have h3 : Entails.eval a c5423 := h 5422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7562 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5423, some c5342, some c5246, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7562 : lratChecker f7562 p7562 = .success := by decide +kernel
theorem unsat7562 : Unsatisfiable (PosFin 65) f7562 := by
  apply lratCheckerSound f7562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7562
  · intro a ha; simp [p7562] at ha; subst a; trivial
  · exact checked7562
theorem derived7562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7562 := by
  apply localUnsat_implies_entails f7562 [c5423, c5342, c5246] c7562 unsat7562 (by rfl) a
  have h0 : Entails.eval a c5423 := h 5422 (by decide)
  have h1 : Entails.eval a c5342 := h 5341 (by decide)
  have h2 : Entails.eval a c5246 := h 5245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7563 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5147, some c5133, some c5539, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7563 : lratChecker f7563 p7563 = .success := by decide +kernel
theorem unsat7563 : Unsatisfiable (PosFin 65) f7563 := by
  apply lratCheckerSound f7563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7563
  · intro a ha; simp [p7563] at ha; subst a; trivial
  · exact checked7563
theorem derived7563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7563 := by
  apply localUnsat_implies_entails f7563 [c5147, c5133, c5539] c7563 unsat7563 (by rfl) a
  have h0 : Entails.eval a c5147 := h 5146 (by decide)
  have h1 : Entails.eval a c5133 := h 5132 (by decide)
  have h2 : Entails.eval a c5539 := h 5538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7564 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7560, some c7559, some c6355, some c6340, some c6296, some c7470, some c7320, some c7423, some c7058, some c6929, some c7561, some c7563, some c7562, some c5195, some c5255, some c5720, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7564 : lratChecker f7564 p7564 = .success := by decide +kernel
theorem unsat7564 : Unsatisfiable (PosFin 65) f7564 := by
  apply lratCheckerSound f7564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7564
  · intro a ha; simp [p7564] at ha; subst a; trivial
  · exact checked7564
theorem derived7564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7564 := by
  apply localUnsat_implies_entails f7564 [c7560, c7559, c6355, c6340, c6296, c7470, c7320, c7423, c7058, c6929, c7561, c7563, c7562, c5195, c5255, c5720] c7564 unsat7564 (by rfl) a
  have h0 : Entails.eval a c7560 := derived7560 a h
  have h1 : Entails.eval a c7559 := derived7559 a h
  have h2 : Entails.eval a c6355 := h 6354 (by decide)
  have h3 : Entails.eval a c6340 := h 6339 (by decide)
  have h4 : Entails.eval a c6296 := h 6295 (by decide)
  have h5 : Entails.eval a c7470 := h 7469 (by decide)
  have h6 : Entails.eval a c7320 := h 7319 (by decide)
  have h7 : Entails.eval a c7423 := h 7422 (by decide)
  have h8 : Entails.eval a c7058 := h 7057 (by decide)
  have h9 : Entails.eval a c6929 := h 6928 (by decide)
  have h10 : Entails.eval a c7561 := derived7561 a h
  have h11 : Entails.eval a c7563 := derived7563 a h
  have h12 : Entails.eval a c7562 := derived7562 a h
  have h13 : Entails.eval a c5195 := h 5194 (by decide)
  have h14 : Entails.eval a c5255 := h 5254 (by decide)
  have h15 : Entails.eval a c5720 := h 5719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7565 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7058, some c7035, some c6543, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7565 : lratChecker f7565 p7565 = .success := by decide +kernel
theorem unsat7565 : Unsatisfiable (PosFin 65) f7565 := by
  apply lratCheckerSound f7565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7565
  · intro a ha; simp [p7565] at ha; subst a; trivial
  · exact checked7565
theorem derived7565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7565 := by
  apply localUnsat_implies_entails f7565 [c7058, c7035, c6543] c7565 unsat7565 (by rfl) a
  have h0 : Entails.eval a c7058 := h 7057 (by decide)
  have h1 : Entails.eval a c7035 := h 7034 (by decide)
  have h2 : Entails.eval a c6543 := h 6542 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7566 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7559, some c7564, some c7565, some c6416, some c6482, some c6666, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7566 : lratChecker f7566 p7566 = .success := by decide +kernel
theorem unsat7566 : Unsatisfiable (PosFin 65) f7566 := by
  apply lratCheckerSound f7566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7566
  · intro a ha; simp [p7566] at ha; subst a; trivial
  · exact checked7566
theorem derived7566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7566 := by
  apply localUnsat_implies_entails f7566 [c7559, c7564, c7565, c6416, c6482, c6666] c7566 unsat7566 (by rfl) a
  have h0 : Entails.eval a c7559 := derived7559 a h
  have h1 : Entails.eval a c7564 := derived7564 a h
  have h2 : Entails.eval a c7565 := derived7565 a h
  have h3 : Entails.eval a c6416 := h 6415 (by decide)
  have h4 : Entails.eval a c6482 := h 6481 (by decide)
  have h5 : Entails.eval a c6666 := h 6665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7567 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨36, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7091, some c6340, some c6998, some c6469, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7567 : lratChecker f7567 p7567 = .success := by decide +kernel
theorem unsat7567 : Unsatisfiable (PosFin 65) f7567 := by
  apply lratCheckerSound f7567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7567
  · intro a ha; simp [p7567] at ha; subst a; trivial
  · exact checked7567
theorem derived7567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7567 := by
  apply localUnsat_implies_entails f7567 [c7091, c6340, c6998, c6469] c7567 unsat7567 (by rfl) a
  have h0 : Entails.eval a c7091 := h 7090 (by decide)
  have h1 : Entails.eval a c6340 := h 6339 (by decide)
  have h2 : Entails.eval a c6998 := h 6997 (by decide)
  have h3 : Entails.eval a c6469 := h 6468 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7568 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7559, some c7560, some c7566, some c7567, some c6728, some c6590, some c6810, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7568 : lratChecker f7568 p7568 = .success := by decide +kernel
theorem unsat7568 : Unsatisfiable (PosFin 65) f7568 := by
  apply lratCheckerSound f7568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7568
  · intro a ha; simp [p7568] at ha; subst a; trivial
  · exact checked7568
theorem derived7568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7568 := by
  apply localUnsat_implies_entails f7568 [c7559, c7560, c7566, c7567, c6728, c6590, c6810] c7568 unsat7568 (by rfl) a
  have h0 : Entails.eval a c7559 := derived7559 a h
  have h1 : Entails.eval a c7560 := derived7560 a h
  have h2 : Entails.eval a c7566 := derived7566 a h
  have h3 : Entails.eval a c7567 := derived7567 a h
  have h4 : Entails.eval a c6728 := h 6727 (by decide)
  have h5 : Entails.eval a c6590 := h 6589 (by decide)
  have h6 : Entails.eval a c6810 := h 6809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7569 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨42, by decide⟩, true), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6729, some c6591, some c6812, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7569 : lratChecker f7569 p7569 = .success := by decide +kernel
theorem unsat7569 : Unsatisfiable (PosFin 65) f7569 := by
  apply lratCheckerSound f7569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7569
  · intro a ha; simp [p7569] at ha; subst a; trivial
  · exact checked7569
theorem derived7569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7569 := by
  apply localUnsat_implies_entails f7569 [c6729, c6591, c6812] c7569 unsat7569 (by rfl) a
  have h0 : Entails.eval a c6729 := h 6728 (by decide)
  have h1 : Entails.eval a c6591 := h 6590 (by decide)
  have h2 : Entails.eval a c6812 := h 6811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7570 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5218, some c5196, some c5255, some c5720, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7570 : lratChecker f7570 p7570 = .success := by decide +kernel
theorem unsat7570 : Unsatisfiable (PosFin 65) f7570 := by
  apply lratCheckerSound f7570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7570
  · intro a ha; simp [p7570] at ha; subst a; trivial
  · exact checked7570
theorem derived7570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7570 := by
  apply localUnsat_implies_entails f7570 [c5218, c5196, c5255, c5720] c7570 unsat7570 (by rfl) a
  have h0 : Entails.eval a c5218 := h 5217 (by decide)
  have h1 : Entails.eval a c5196 := h 5195 (by decide)
  have h2 : Entails.eval a c5255 := h 5254 (by decide)
  have h3 : Entails.eval a c5720 := h 5719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7571 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5539, some c5720, some c5170, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7571 : lratChecker f7571 p7571 = .success := by decide +kernel
theorem unsat7571 : Unsatisfiable (PosFin 65) f7571 := by
  apply lratCheckerSound f7571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7571
  · intro a ha; simp [p7571] at ha; subst a; trivial
  · exact checked7571
theorem derived7571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7571 := by
  apply localUnsat_implies_entails f7571 [c5539, c5720, c5170] c7571 unsat7571 (by rfl) a
  have h0 : Entails.eval a c5539 := h 5538 (by decide)
  have h1 : Entails.eval a c5720 := h 5719 (by decide)
  have h2 : Entails.eval a c5170 := h 5169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7572 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨57, by decide⟩, true), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5186, some c5150, some c7556, some c5331, some c5333, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7572 : lratChecker f7572 p7572 = .success := by decide +kernel
theorem unsat7572 : Unsatisfiable (PosFin 65) f7572 := by
  apply lratCheckerSound f7572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7572
  · intro a ha; simp [p7572] at ha; subst a; trivial
  · exact checked7572
theorem derived7572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7572 := by
  apply localUnsat_implies_entails f7572 [c5186, c5150, c7556, c5331, c5333] c7572 unsat7572 (by rfl) a
  have h0 : Entails.eval a c5186 := h 5185 (by decide)
  have h1 : Entails.eval a c5150 := h 5149 (by decide)
  have h2 : Entails.eval a c7556 := derived7556 a h
  have h3 : Entails.eval a c5331 := h 5330 (by decide)
  have h4 : Entails.eval a c5333 := h 5332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7573 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨42, by decide⟩, true), (⟨36, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7568, some c6812, some c6824, some c7471, some c7335, some c7037, some c6689, some c7128, some c6528, some c7390, some c7570, some c7572, some c7571, some c5231, some c5163, some c5424, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7573 : lratChecker f7573 p7573 = .success := by decide +kernel
theorem unsat7573 : Unsatisfiable (PosFin 65) f7573 := by
  apply lratCheckerSound f7573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7573
  · intro a ha; simp [p7573] at ha; subst a; trivial
  · exact checked7573
theorem derived7573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7573 := by
  apply localUnsat_implies_entails f7573 [c7569, c7568, c6812, c6824, c7471, c7335, c7037, c6689, c7128, c6528, c7390, c7570, c7572, c7571, c5231, c5163, c5424] c7573 unsat7573 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7568 := derived7568 a h
  have h2 : Entails.eval a c6812 := h 6811 (by decide)
  have h3 : Entails.eval a c6824 := h 6823 (by decide)
  have h4 : Entails.eval a c7471 := h 7470 (by decide)
  have h5 : Entails.eval a c7335 := h 7334 (by decide)
  have h6 : Entails.eval a c7037 := h 7036 (by decide)
  have h7 : Entails.eval a c6689 := h 6688 (by decide)
  have h8 : Entails.eval a c7128 := h 7127 (by decide)
  have h9 : Entails.eval a c6528 := h 6527 (by decide)
  have h10 : Entails.eval a c7390 := h 7389 (by decide)
  have h11 : Entails.eval a c7570 := derived7570 a h
  have h12 : Entails.eval a c7572 := derived7572 a h
  have h13 : Entails.eval a c7571 := derived7571 a h
  have h14 : Entails.eval a c5231 := h 5230 (by decide)
  have h15 : Entails.eval a c5163 := h 5162 (by decide)
  have h16 : Entails.eval a c5424 := h 5423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7574 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨42, by decide⟩, true), (⟨36, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7573, some c6929, some c6901, some c6701, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7574 : lratChecker f7574 p7574 = .success := by decide +kernel
theorem unsat7574 : Unsatisfiable (PosFin 65) f7574 := by
  apply lratCheckerSound f7574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7574
  · intro a ha; simp [p7574] at ha; subst a; trivial
  · exact checked7574
theorem derived7574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7574 := by
  apply localUnsat_implies_entails f7574 [c7569, c7573, c6929, c6901, c6701] c7574 unsat7574 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7573 := derived7573 a h
  have h2 : Entails.eval a c6929 := h 6928 (by decide)
  have h3 : Entails.eval a c6901 := h 6900 (by decide)
  have h4 : Entails.eval a c6701 := h 6700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7575 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨36, by decide⟩, false), (⟨64, by decide⟩, false), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7574, some c7552, some c7240, some c6641, some c6357, some c6701, some c7471, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7575 : lratChecker f7575 p7575 = .success := by decide +kernel
theorem unsat7575 : Unsatisfiable (PosFin 65) f7575 := by
  apply lratCheckerSound f7575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7575
  · intro a ha; simp [p7575] at ha; subst a; trivial
  · exact checked7575
theorem derived7575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7575 := by
  apply localUnsat_implies_entails f7575 [c7574, c7552, c7240, c6641, c6357, c6701, c7471] c7575 unsat7575 (by rfl) a
  have h0 : Entails.eval a c7574 := derived7574 a h
  have h1 : Entails.eval a c7552 := derived7552 a h
  have h2 : Entails.eval a c7240 := h 7239 (by decide)
  have h3 : Entails.eval a c6641 := h 6640 (by decide)
  have h4 : Entails.eval a c6357 := h 6356 (by decide)
  have h5 : Entails.eval a c6701 := h 6700 (by decide)
  have h6 : Entails.eval a c7471 := h 7470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7576 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7575, some c7092, some c6342, some c6999, some c6471, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7576 : lratChecker f7576 p7576 = .success := by decide +kernel
theorem unsat7576 : Unsatisfiable (PosFin 65) f7576 := by
  apply lratCheckerSound f7576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7576
  · intro a ha; simp [p7576] at ha; subst a; trivial
  · exact checked7576
theorem derived7576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7576 := by
  apply localUnsat_implies_entails f7576 [c7575, c7092, c6342, c6999, c6471] c7576 unsat7576 (by rfl) a
  have h0 : Entails.eval a c7575 := derived7575 a h
  have h1 : Entails.eval a c7092 := h 7091 (by decide)
  have h2 : Entails.eval a c6342 := h 6341 (by decide)
  have h3 : Entails.eval a c6999 := h 6998 (by decide)
  have h4 : Entails.eval a c6471 := h 6470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7577 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6471, some c6456, some c7171, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7577 : lratChecker f7577 p7577 = .success := by decide +kernel
theorem unsat7577 : Unsatisfiable (PosFin 65) f7577 := by
  apply lratCheckerSound f7577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7577
  · intro a ha; simp [p7577] at ha; subst a; trivial
  · exact checked7577
theorem derived7577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7577 := by
  apply localUnsat_implies_entails f7577 [c6471, c6456, c7171] c7577 unsat7577 (by rfl) a
  have h0 : Entails.eval a c6471 := h 6470 (by decide)
  have h1 : Entails.eval a c6456 := h 6455 (by decide)
  have h2 : Entails.eval a c7171 := h 7170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7578 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨36, by decide⟩, true), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7270, some c7404, some c6990, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7578 : lratChecker f7578 p7578 = .success := by decide +kernel
theorem unsat7578 : Unsatisfiable (PosFin 65) f7578 := by
  apply lratCheckerSound f7578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7578
  · intro a ha; simp [p7578] at ha; subst a; trivial
  · exact checked7578
theorem derived7578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7578 := by
  apply localUnsat_implies_entails f7578 [c7270, c7404, c6990] c7578 unsat7578 (by rfl) a
  have h0 : Entails.eval a c7270 := h 7269 (by decide)
  have h1 : Entails.eval a c7404 := h 7403 (by decide)
  have h2 : Entails.eval a c6990 := h 6989 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7579 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨58, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7552, some c7577, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7579 : lratChecker f7579 p7579 = .success := by decide +kernel
theorem unsat7579 : Unsatisfiable (PosFin 65) f7579 := by
  apply lratCheckerSound f7579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7579
  · intro a ha; simp [p7579] at ha; subst a; trivial
  · exact checked7579
theorem derived7579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7579 := by
  apply localUnsat_implies_entails f7579 [c7552, c7577] c7579 unsat7579 (by rfl) a
  have h0 : Entails.eval a c7552 := derived7552 a h
  have h1 : Entails.eval a c7577 := derived7577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7580 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨36, by decide⟩, true), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7578, some c7579, some c6495, some c6511, some c7071, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7580 : lratChecker f7580 p7580 = .success := by decide +kernel
theorem unsat7580 : Unsatisfiable (PosFin 65) f7580 := by
  apply lratCheckerSound f7580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7580
  · intro a ha; simp [p7580] at ha; subst a; trivial
  · exact checked7580
theorem derived7580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7580 := by
  apply localUnsat_implies_entails f7580 [c7578, c7579, c6495, c6511, c7071] c7580 unsat7580 (by rfl) a
  have h0 : Entails.eval a c7578 := derived7578 a h
  have h1 : Entails.eval a c7579 := derived7579 a h
  have h2 : Entails.eval a c6495 := h 6494 (by decide)
  have h3 : Entails.eval a c6511 := h 6510 (by decide)
  have h4 : Entails.eval a c7071 := h 7070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7581 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨36, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6297, some c6326, some c6573, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7581 : lratChecker f7581 p7581 = .success := by decide +kernel
theorem unsat7581 : Unsatisfiable (PosFin 65) f7581 := by
  apply lratCheckerSound f7581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7581
  · intro a ha; simp [p7581] at ha; subst a; trivial
  · exact checked7581
theorem derived7581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7581 := by
  apply localUnsat_implies_entails f7581 [c6297, c6326, c6573] c7581 unsat7581 (by rfl) a
  have h0 : Entails.eval a c6297 := h 6296 (by decide)
  have h1 : Entails.eval a c6326 := h 6325 (by decide)
  have h2 : Entails.eval a c6573 := h 6572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7582 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨36, by decide⟩, true), (⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6969, some c6983, some c7071, some c7128, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7582 : lratChecker f7582 p7582 = .success := by decide +kernel
theorem unsat7582 : Unsatisfiable (PosFin 65) f7582 := by
  apply lratCheckerSound f7582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7582
  · intro a ha; simp [p7582] at ha; subst a; trivial
  · exact checked7582
theorem derived7582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7582 := by
  apply localUnsat_implies_entails f7582 [c6969, c6983, c7071, c7128] c7582 unsat7582 (by rfl) a
  have h0 : Entails.eval a c6969 := h 6968 (by decide)
  have h1 : Entails.eval a c6983 := h 6982 (by decide)
  have h2 : Entails.eval a c7071 := h 7070 (by decide)
  have h3 : Entails.eval a c7128 := h 7127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7583 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7576, some c7580, some c7582, some c7581, some c7552, some c7569, some c6689, some c7471, some c6901, some c6812, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7583 : lratChecker f7583 p7583 = .success := by decide +kernel
theorem unsat7583 : Unsatisfiable (PosFin 65) f7583 := by
  apply lratCheckerSound f7583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7583
  · intro a ha; simp [p7583] at ha; subst a; trivial
  · exact checked7583
theorem derived7583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7583 := by
  apply localUnsat_implies_entails f7583 [c7576, c7580, c7582, c7581, c7552, c7569, c6689, c7471, c6901, c6812] c7583 unsat7583 (by rfl) a
  have h0 : Entails.eval a c7576 := derived7576 a h
  have h1 : Entails.eval a c7580 := derived7580 a h
  have h2 : Entails.eval a c7582 := derived7582 a h
  have h3 : Entails.eval a c7581 := derived7581 a h
  have h4 : Entails.eval a c7552 := derived7552 a h
  have h5 : Entails.eval a c7569 := derived7569 a h
  have h6 : Entails.eval a c6689 := h 6688 (by decide)
  have h7 : Entails.eval a c7471 := h 7470 (by decide)
  have h8 : Entails.eval a c6901 := h 6900 (by decide)
  have h9 : Entails.eval a c6812 := h 6811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7584 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7145, some c7129, some c6528, some c6793, some c6825, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7584 : lratChecker f7584 p7584 = .success := by decide +kernel
theorem unsat7584 : Unsatisfiable (PosFin 65) f7584 := by
  apply lratCheckerSound f7584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7584
  · intro a ha; simp [p7584] at ha; subst a; trivial
  · exact checked7584
theorem derived7584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7584 := by
  apply localUnsat_implies_entails f7584 [c7145, c7129, c6528, c6793, c6825] c7584 unsat7584 (by rfl) a
  have h0 : Entails.eval a c7145 := h 7144 (by decide)
  have h1 : Entails.eval a c7129 := h 7128 (by decide)
  have h2 : Entails.eval a c6528 := h 6527 (by decide)
  have h3 : Entails.eval a c6793 := h 6792 (by decide)
  have h4 : Entails.eval a c6825 := h 6824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7585 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false), (⟨36, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7584, some c6776, some c6991, some c6825, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7585 : lratChecker f7585 p7585 = .success := by decide +kernel
theorem unsat7585 : Unsatisfiable (PosFin 65) f7585 := by
  apply lratCheckerSound f7585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7585
  · intro a ha; simp [p7585] at ha; subst a; trivial
  · exact checked7585
theorem derived7585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7585 := by
  apply localUnsat_implies_entails f7585 [c7584, c6776, c6991, c6825] c7585 unsat7585 (by rfl) a
  have h0 : Entails.eval a c7584 := derived7584 a h
  have h1 : Entails.eval a c6776 := h 6775 (by decide)
  have h2 : Entails.eval a c6991 := h 6990 (by decide)
  have h3 : Entails.eval a c6825 := h 6824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7586 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5324, some c5426, some c5438, some c6043, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7586 : lratChecker f7586 p7586 = .success := by decide +kernel
theorem unsat7586 : Unsatisfiable (PosFin 65) f7586 := by
  apply lratCheckerSound f7586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7586
  · intro a ha; simp [p7586] at ha; subst a; trivial
  · exact checked7586
theorem derived7586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7586 := by
  apply localUnsat_implies_entails f7586 [c5324, c5426, c5438, c6043] c7586 unsat7586 (by rfl) a
  have h0 : Entails.eval a c5324 := h 5323 (by decide)
  have h1 : Entails.eval a c5426 := h 5425 (by decide)
  have h2 : Entails.eval a c5438 := h 5437 (by decide)
  have h3 : Entails.eval a c6043 := h 6042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7587 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7586, some c5323, some c5315, some c5625, some c5786, some c5176, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7587 : lratChecker f7587 p7587 = .success := by decide +kernel
theorem unsat7587 : Unsatisfiable (PosFin 65) f7587 := by
  apply lratCheckerSound f7587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7587
  · intro a ha; simp [p7587] at ha; subst a; trivial
  · exact checked7587
theorem derived7587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7587 := by
  apply localUnsat_implies_entails f7587 [c7586, c5323, c5315, c5625, c5786, c5176] c7587 unsat7587 (by rfl) a
  have h0 : Entails.eval a c7586 := derived7586 a h
  have h1 : Entails.eval a c5323 := h 5322 (by decide)
  have h2 : Entails.eval a c5315 := h 5314 (by decide)
  have h3 : Entails.eval a c5625 := h 5624 (by decide)
  have h4 : Entails.eval a c5786 := h 5785 (by decide)
  have h5 : Entails.eval a c5176 := h 5175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7588 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, false), (⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨39, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7587, some c5259, some c5875, some c5795, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7588 : lratChecker f7588 p7588 = .success := by decide +kernel
theorem unsat7588 : Unsatisfiable (PosFin 65) f7588 := by
  apply lratCheckerSound f7588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7588
  · intro a ha; simp [p7588] at ha; subst a; trivial
  · exact checked7588
theorem derived7588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7588 := by
  apply localUnsat_implies_entails f7588 [c7587, c5259, c5875, c5795] c7588 unsat7588 (by rfl) a
  have h0 : Entails.eval a c7587 := derived7587 a h
  have h1 : Entails.eval a c5259 := h 5258 (by decide)
  have h2 : Entails.eval a c5875 := h 5874 (by decide)
  have h3 : Entails.eval a c5795 := h 5794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7589 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6366, some c5202, some c5203, some c5198, some c6158, some c6159, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7589 : lratChecker f7589 p7589 = .success := by decide +kernel
theorem unsat7589 : Unsatisfiable (PosFin 65) f7589 := by
  apply lratCheckerSound f7589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7589
  · intro a ha; simp [p7589] at ha; subst a; trivial
  · exact checked7589
theorem derived7589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7589 := by
  apply localUnsat_implies_entails f7589 [c6366, c5202, c5203, c5198, c6158, c6159] c7589 unsat7589 (by rfl) a
  have h0 : Entails.eval a c6366 := h 6365 (by decide)
  have h1 : Entails.eval a c5202 := h 5201 (by decide)
  have h2 : Entails.eval a c5203 := h 5202 (by decide)
  have h3 : Entails.eval a c5198 := h 5197 (by decide)
  have h4 : Entails.eval a c6158 := h 6157 (by decide)
  have h5 : Entails.eval a c6159 := h 6158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7590 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨36, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7581, some c7585, some c6612, some c6401, some c6366, some c6689, some c7431, some c6712, some c6418, some c6528, some c6793, some c7270, some c7471, some c7589, some c7588, some c5506, some c5698, some c5171, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7590 : lratChecker f7590 p7590 = .success := by decide +kernel
theorem unsat7590 : Unsatisfiable (PosFin 65) f7590 := by
  apply lratCheckerSound f7590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7590
  · intro a ha; simp [p7590] at ha; subst a; trivial
  · exact checked7590
theorem derived7590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7590 := by
  apply localUnsat_implies_entails f7590 [c7581, c7585, c6612, c6401, c6366, c6689, c7431, c6712, c6418, c6528, c6793, c7270, c7471, c7589, c7588, c5506, c5698, c5171] c7590 unsat7590 (by rfl) a
  have h0 : Entails.eval a c7581 := derived7581 a h
  have h1 : Entails.eval a c7585 := derived7585 a h
  have h2 : Entails.eval a c6612 := h 6611 (by decide)
  have h3 : Entails.eval a c6401 := h 6400 (by decide)
  have h4 : Entails.eval a c6366 := h 6365 (by decide)
  have h5 : Entails.eval a c6689 := h 6688 (by decide)
  have h6 : Entails.eval a c7431 := h 7430 (by decide)
  have h7 : Entails.eval a c6712 := h 6711 (by decide)
  have h8 : Entails.eval a c6418 := h 6417 (by decide)
  have h9 : Entails.eval a c6528 := h 6527 (by decide)
  have h10 : Entails.eval a c6793 := h 6792 (by decide)
  have h11 : Entails.eval a c7270 := h 7269 (by decide)
  have h12 : Entails.eval a c7471 := h 7470 (by decide)
  have h13 : Entails.eval a c7589 := derived7589 a h
  have h14 : Entails.eval a c7588 := derived7588 a h
  have h15 : Entails.eval a c5506 := h 5505 (by decide)
  have h16 : Entails.eval a c5698 := h 5697 (by decide)
  have h17 : Entails.eval a c5171 := h 5170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7591 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨36, by decide⟩, true), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6969, some c6983, some c7071, some c7129, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7591 : lratChecker f7591 p7591 = .success := by decide +kernel
theorem unsat7591 : Unsatisfiable (PosFin 65) f7591 := by
  apply lratCheckerSound f7591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7591
  · intro a ha; simp [p7591] at ha; subst a; trivial
  · exact checked7591
theorem derived7591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7591 := by
  apply localUnsat_implies_entails f7591 [c6969, c6983, c7071, c7129] c7591 unsat7591 (by rfl) a
  have h0 : Entails.eval a c6969 := h 6968 (by decide)
  have h1 : Entails.eval a c6983 := h 6982 (by decide)
  have h2 : Entails.eval a c7071 := h 7070 (by decide)
  have h3 : Entails.eval a c7129 := h 7128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7592 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7590, some c7591, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7592 : lratChecker f7592 p7592 = .success := by decide +kernel
theorem unsat7592 : Unsatisfiable (PosFin 65) f7592 := by
  apply lratCheckerSound f7592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7592
  · intro a ha; simp [p7592] at ha; subst a; trivial
  · exact checked7592
theorem derived7592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7592 := by
  apply localUnsat_implies_entails f7592 [c7590, c7591] c7592 unsat7592 (by rfl) a
  have h0 : Entails.eval a c7590 := derived7590 a h
  have h1 : Entails.eval a c7591 := derived7591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7593 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7195, some c7129, some c7210, some c7336, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7593 : lratChecker f7593 p7593 = .success := by decide +kernel
theorem unsat7593 : Unsatisfiable (PosFin 65) f7593 := by
  apply lratCheckerSound f7593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7593
  · intro a ha; simp [p7593] at ha; subst a; trivial
  · exact checked7593
theorem derived7593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7593 := by
  apply localUnsat_implies_entails f7593 [c7195, c7129, c7210, c7336] c7593 unsat7593 (by rfl) a
  have h0 : Entails.eval a c7195 := h 7194 (by decide)
  have h1 : Entails.eval a c7129 := h 7128 (by decide)
  have h2 : Entails.eval a c7210 := h 7209 (by decide)
  have h3 : Entails.eval a c7336 := h 7335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7594 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5539, some c5720, some c5171, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7594 : lratChecker f7594 p7594 = .success := by decide +kernel
theorem unsat7594 : Unsatisfiable (PosFin 65) f7594 := by
  apply lratCheckerSound f7594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7594
  · intro a ha; simp [p7594] at ha; subst a; trivial
  · exact checked7594
theorem derived7594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7594 := by
  apply localUnsat_implies_entails f7594 [c5539, c5720, c5171] c7594 unsat7594 (by rfl) a
  have h0 : Entails.eval a c5539 := h 5538 (by decide)
  have h1 : Entails.eval a c5720 := h 5719 (by decide)
  have h2 : Entails.eval a c5171 := h 5170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7595 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨39, by decide⟩, false), (⟨37, by decide⟩, false), (⟨58, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5198, some c5187, some c5150, some c7556, some c5332, some c5333, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7595 : lratChecker f7595 p7595 = .success := by decide +kernel
theorem unsat7595 : Unsatisfiable (PosFin 65) f7595 := by
  apply lratCheckerSound f7595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7595
  · intro a ha; simp [p7595] at ha; subst a; trivial
  · exact checked7595
theorem derived7595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7595 := by
  apply localUnsat_implies_entails f7595 [c5198, c5187, c5150, c7556, c5332, c5333] c7595 unsat7595 (by rfl) a
  have h0 : Entails.eval a c5198 := h 5197 (by decide)
  have h1 : Entails.eval a c5187 := h 5186 (by decide)
  have h2 : Entails.eval a c5150 := h 5149 (by decide)
  have h3 : Entails.eval a c7556 := derived7556 a h
  have h4 : Entails.eval a c5332 := h 5331 (by decide)
  have h5 : Entails.eval a c5333 := h 5332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7596 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨44, by decide⟩, true), (⟨58, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7592, some c7593, some c7390, some c7023, some c6999, some c6929, some c7356, some c6813, some c6825, some c7145, some c7471, some c6729, some c6528, some c7595, some c7594, some c5219, some c5232, some c5163, some c5426, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7596 : lratChecker f7596 p7596 = .success := by decide +kernel
theorem unsat7596 : Unsatisfiable (PosFin 65) f7596 := by
  apply lratCheckerSound f7596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7596
  · intro a ha; simp [p7596] at ha; subst a; trivial
  · exact checked7596
theorem derived7596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7596 := by
  apply localUnsat_implies_entails f7596 [c7592, c7593, c7390, c7023, c6999, c6929, c7356, c6813, c6825, c7145, c7471, c6729, c6528, c7595, c7594, c5219, c5232, c5163, c5426] c7596 unsat7596 (by rfl) a
  have h0 : Entails.eval a c7592 := derived7592 a h
  have h1 : Entails.eval a c7593 := derived7593 a h
  have h2 : Entails.eval a c7390 := h 7389 (by decide)
  have h3 : Entails.eval a c7023 := h 7022 (by decide)
  have h4 : Entails.eval a c6999 := h 6998 (by decide)
  have h5 : Entails.eval a c6929 := h 6928 (by decide)
  have h6 : Entails.eval a c7356 := h 7355 (by decide)
  have h7 : Entails.eval a c6813 := h 6812 (by decide)
  have h8 : Entails.eval a c6825 := h 6824 (by decide)
  have h9 : Entails.eval a c7145 := h 7144 (by decide)
  have h10 : Entails.eval a c7471 := h 7470 (by decide)
  have h11 : Entails.eval a c6729 := h 6728 (by decide)
  have h12 : Entails.eval a c6528 := h 6527 (by decide)
  have h13 : Entails.eval a c7595 := derived7595 a h
  have h14 : Entails.eval a c7594 := derived7594 a h
  have h15 : Entails.eval a c5219 := h 5218 (by decide)
  have h16 : Entails.eval a c5232 := h 5231 (by decide)
  have h17 : Entails.eval a c5163 := h 5162 (by decide)
  have h18 : Entails.eval a c5426 := h 5425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7597 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨58, by decide⟩, true), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7592, some c7596, some c7156, some c7260, some c7023, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7597 : lratChecker f7597 p7597 = .success := by decide +kernel
theorem unsat7597 : Unsatisfiable (PosFin 65) f7597 := by
  apply lratCheckerSound f7597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7597
  · intro a ha; simp [p7597] at ha; subst a; trivial
  · exact checked7597
theorem derived7597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7597 := by
  apply localUnsat_implies_entails f7597 [c7592, c7596, c7156, c7260, c7023] c7597 unsat7597 (by rfl) a
  have h0 : Entails.eval a c7592 := derived7592 a h
  have h1 : Entails.eval a c7596 := derived7596 a h
  have h2 : Entails.eval a c7156 := h 7155 (by decide)
  have h3 : Entails.eval a c7260 := h 7259 (by decide)
  have h4 : Entails.eval a c7023 := h 7022 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7598 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨36, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7106, some c7023, some c7059, some c7379, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7598 : lratChecker f7598 p7598 = .success := by decide +kernel
theorem unsat7598 : Unsatisfiable (PosFin 65) f7598 := by
  apply lratCheckerSound f7598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7598
  · intro a ha; simp [p7598] at ha; subst a; trivial
  · exact checked7598
theorem derived7598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7598 := by
  apply localUnsat_implies_entails f7598 [c7106, c7023, c7059, c7379] c7598 unsat7598 (by rfl) a
  have h0 : Entails.eval a c7106 := h 7105 (by decide)
  have h1 : Entails.eval a c7023 := h 7022 (by decide)
  have h2 : Entails.eval a c7059 := h 7058 (by decide)
  have h3 : Entails.eval a c7379 := h 7378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7599 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7379, some c6674, some c6689, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7599 : lratChecker f7599 p7599 = .success := by decide +kernel
theorem unsat7599 : Unsatisfiable (PosFin 65) f7599 := by
  apply lratCheckerSound f7599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7599
  · intro a ha; simp [p7599] at ha; subst a; trivial
  · exact checked7599
theorem derived7599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7599 := by
  apply localUnsat_implies_entails f7599 [c7379, c6674, c6689] c7599 unsat7599 (by rfl) a
  have h0 : Entails.eval a c7379 := h 7378 (by decide)
  have h1 : Entails.eval a c6674 := h 6673 (by decide)
  have h2 : Entails.eval a c6689 := h 6688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7600 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨44, by decide⟩, false), (⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7592, some c7598, some c7599, some c6358, some c6401, some c6445, some c6472, some c7145, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7600 : lratChecker f7600 p7600 = .success := by decide +kernel
theorem unsat7600 : Unsatisfiable (PosFin 65) f7600 := by
  apply lratCheckerSound f7600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7600
  · intro a ha; simp [p7600] at ha; subst a; trivial
  · exact checked7600
theorem derived7600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7600 := by
  apply localUnsat_implies_entails f7600 [c7592, c7598, c7599, c6358, c6401, c6445, c6472, c7145] c7600 unsat7600 (by rfl) a
  have h0 : Entails.eval a c7592 := derived7592 a h
  have h1 : Entails.eval a c7598 := derived7598 a h
  have h2 : Entails.eval a c7599 := derived7599 a h
  have h3 : Entails.eval a c6358 := h 6357 (by decide)
  have h4 : Entails.eval a c6401 := h 6400 (by decide)
  have h5 : Entails.eval a c6445 := h 6444 (by decide)
  have h6 : Entails.eval a c6472 := h 6471 (by decide)
  have h7 : Entails.eval a c7145 := h 7144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7601 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨60, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false), (⟨62, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7583, some c7592, some c7597, some c7598, some c7600, some c6999, some c7240, some c6929, some c6813, some c6825, some c6326, some c7471, some c6528, some c7038, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7601 : lratChecker f7601 p7601 = .success := by decide +kernel
theorem unsat7601 : Unsatisfiable (PosFin 65) f7601 := by
  apply lratCheckerSound f7601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7601
  · intro a ha; simp [p7601] at ha; subst a; trivial
  · exact checked7601
theorem derived7601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7601 := by
  apply localUnsat_implies_entails f7601 [c7583, c7592, c7597, c7598, c7600, c6999, c7240, c6929, c6813, c6825, c6326, c7471, c6528, c7038] c7601 unsat7601 (by rfl) a
  have h0 : Entails.eval a c7583 := derived7583 a h
  have h1 : Entails.eval a c7592 := derived7592 a h
  have h2 : Entails.eval a c7597 := derived7597 a h
  have h3 : Entails.eval a c7598 := derived7598 a h
  have h4 : Entails.eval a c7600 := derived7600 a h
  have h5 : Entails.eval a c6999 := h 6998 (by decide)
  have h6 : Entails.eval a c7240 := h 7239 (by decide)
  have h7 : Entails.eval a c6929 := h 6928 (by decide)
  have h8 : Entails.eval a c6813 := h 6812 (by decide)
  have h9 : Entails.eval a c6825 := h 6824 (by decide)
  have h10 : Entails.eval a c6326 := h 6325 (by decide)
  have h11 : Entails.eval a c7471 := h 7470 (by decide)
  have h12 : Entails.eval a c6528 := h 6527 (by decide)
  have h13 : Entails.eval a c7038 := h 7037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7602 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, true), (⟨37, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7140, some c7144, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7602 : lratChecker f7602 p7602 = .success := by decide +kernel
theorem unsat7602 : Unsatisfiable (PosFin 65) f7602 := by
  apply lratCheckerSound f7602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7602
  · intro a ha; simp [p7602] at ha; subst a; trivial
  · exact checked7602
theorem derived7602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7602 := by
  apply localUnsat_implies_entails f7602 [c7140, c7144] c7602 unsat7602 (by rfl) a
  have h0 : Entails.eval a c7140 := h 7139 (by decide)
  have h1 : Entails.eval a c7144 := h 7143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7603 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6522, some c6542, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7603 : lratChecker f7603 p7603 = .success := by decide +kernel
theorem unsat7603 : Unsatisfiable (PosFin 65) f7603 := by
  apply lratCheckerSound f7603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7603
  · intro a ha; simp [p7603] at ha; subst a; trivial
  · exact checked7603
theorem derived7603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7603 := by
  apply localUnsat_implies_entails f7603 [c6522, c6542] c7603 unsat7603 (by rfl) a
  have h0 : Entails.eval a c6522 := h 6521 (by decide)
  have h1 : Entails.eval a c6542 := h 6541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7604 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7601, some c7241, some c6930, some c7471, some c6729, some c6827, some c6683, some c6685, some c7336, some c7602, some c7603, some c6322, some c6295, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7604 : lratChecker f7604 p7604 = .success := by decide +kernel
theorem unsat7604 : Unsatisfiable (PosFin 65) f7604 := by
  apply lratCheckerSound f7604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7604
  · intro a ha; simp [p7604] at ha; subst a; trivial
  · exact checked7604
theorem derived7604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7604 := by
  apply localUnsat_implies_entails f7604 [c7601, c7241, c6930, c7471, c6729, c6827, c6683, c6685, c7336, c7602, c7603, c6322, c6295] c7604 unsat7604 (by rfl) a
  have h0 : Entails.eval a c7601 := derived7601 a h
  have h1 : Entails.eval a c7241 := h 7240 (by decide)
  have h2 : Entails.eval a c6930 := h 6929 (by decide)
  have h3 : Entails.eval a c7471 := h 7470 (by decide)
  have h4 : Entails.eval a c6729 := h 6728 (by decide)
  have h5 : Entails.eval a c6827 := h 6826 (by decide)
  have h6 : Entails.eval a c6683 := h 6682 (by decide)
  have h7 : Entails.eval a c6685 := h 6684 (by decide)
  have h8 : Entails.eval a c7336 := h 7335 (by decide)
  have h9 : Entails.eval a c7602 := derived7602 a h
  have h10 : Entails.eval a c7603 := derived7603 a h
  have h11 : Entails.eval a c6322 := h 6321 (by decide)
  have h12 : Entails.eval a c6295 := h 6294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7605 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨39, by decide⟩, false), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7001, some c7272, some c7406, some c6993, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7605 : lratChecker f7605 p7605 = .success := by decide +kernel
theorem unsat7605 : Unsatisfiable (PosFin 65) f7605 := by
  apply lratCheckerSound f7605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7605
  · intro a ha; simp [p7605] at ha; subst a; trivial
  · exact checked7605
theorem derived7605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7605 := by
  apply localUnsat_implies_entails f7605 [c7001, c7272, c7406, c6993] c7605 unsat7605 (by rfl) a
  have h0 : Entails.eval a c7001 := h 7000 (by decide)
  have h1 : Entails.eval a c7272 := h 7271 (by decide)
  have h2 : Entails.eval a c7406 := h 7405 (by decide)
  have h3 : Entails.eval a c6993 := h 6992 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7606 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7067, some c7069, some c7063, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7606 : lratChecker f7606 p7606 = .success := by decide +kernel
theorem unsat7606 : Unsatisfiable (PosFin 65) f7606 := by
  apply lratCheckerSound f7606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7606
  · intro a ha; simp [p7606] at ha; subst a; trivial
  · exact checked7606
theorem derived7606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7606 := by
  apply localUnsat_implies_entails f7606 [c7067, c7069, c7063] c7606 unsat7606 (by rfl) a
  have h0 : Entails.eval a c7067 := h 7066 (by decide)
  have h1 : Entails.eval a c7069 := h 7068 (by decide)
  have h2 : Entails.eval a c7063 := h 7062 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7607 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5337, some c5427, some c5242, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7607 : lratChecker f7607 p7607 = .success := by decide +kernel
theorem unsat7607 : Unsatisfiable (PosFin 65) f7607 := by
  apply lratCheckerSound f7607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7607
  · intro a ha; simp [p7607] at ha; subst a; trivial
  · exact checked7607
theorem derived7607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7607 := by
  apply localUnsat_implies_entails f7607 [c5337, c5427, c5242] c7607 unsat7607 (by rfl) a
  have h0 : Entails.eval a c5337 := h 5336 (by decide)
  have h1 : Entails.eval a c5427 := h 5426 (by decide)
  have h2 : Entails.eval a c5242 := h 5241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7608 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨58, by decide⟩, true), (⟨56, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5132, some c5146, some c5539, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7608 : lratChecker f7608 p7608 = .success := by decide +kernel
theorem unsat7608 : Unsatisfiable (PosFin 65) f7608 := by
  apply lratCheckerSound f7608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7608
  · intro a ha; simp [p7608] at ha; subst a; trivial
  · exact checked7608
theorem derived7608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7608 := by
  apply localUnsat_implies_entails f7608 [c5132, c5146, c5539] c7608 unsat7608 (by rfl) a
  have h0 : Entails.eval a c5132 := h 5131 (by decide)
  have h1 : Entails.eval a c5146 := h 5145 (by decide)
  have h2 : Entails.eval a c5539 := h 5538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7609 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨56, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5129, some c5143, some c5158, some c5539, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7609 : lratChecker f7609 p7609 = .success := by decide +kernel
theorem unsat7609 : Unsatisfiable (PosFin 65) f7609 := by
  apply lratCheckerSound f7609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7609
  · intro a ha; simp [p7609] at ha; subst a; trivial
  · exact checked7609
theorem derived7609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7609 := by
  apply localUnsat_implies_entails f7609 [c5129, c5143, c5158, c5539] c7609 unsat7609 (by rfl) a
  have h0 : Entails.eval a c5129 := h 5128 (by decide)
  have h1 : Entails.eval a c5143 := h 5142 (by decide)
  have h2 : Entails.eval a c5158 := h 5157 (by decide)
  have h3 : Entails.eval a c5539 := h 5538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7610 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨63, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7607, some c5427, some c5347, some c5244, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7610 : lratChecker f7610 p7610 = .success := by decide +kernel
theorem unsat7610 : Unsatisfiable (PosFin 65) f7610 := by
  apply lratCheckerSound f7610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7610
  · intro a ha; simp [p7610] at ha; subst a; trivial
  · exact checked7610
theorem derived7610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7610 := by
  apply localUnsat_implies_entails f7610 [c7607, c5427, c5347, c5244] c7610 unsat7610 (by rfl) a
  have h0 : Entails.eval a c7607 := derived7607 a h
  have h1 : Entails.eval a c5427 := h 5426 (by decide)
  have h2 : Entails.eval a c5347 := h 5346 (by decide)
  have h3 : Entails.eval a c5244 := h 5243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7611 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5221, some c5200, some c5255, some c5704, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7611 : lratChecker f7611 p7611 = .success := by decide +kernel
theorem unsat7611 : Unsatisfiable (PosFin 65) f7611 := by
  apply lratCheckerSound f7611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7611
  · intro a ha; simp [p7611] at ha; subst a; trivial
  · exact checked7611
theorem derived7611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7611 := by
  apply localUnsat_implies_entails f7611 [c5221, c5200, c5255, c5704] c7611 unsat7611 (by rfl) a
  have h0 : Entails.eval a c5221 := h 5220 (by decide)
  have h1 : Entails.eval a c5200 := h 5199 (by decide)
  have h2 : Entails.eval a c5255 := h 5254 (by decide)
  have h3 : Entails.eval a c5704 := h 5703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7612 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7610, some c5427, some c7556, some c7555, some c5222, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7612 : lratChecker f7612 p7612 = .success := by decide +kernel
theorem unsat7612 : Unsatisfiable (PosFin 65) f7612 := by
  apply lratCheckerSound f7612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7612
  · intro a ha; simp [p7612] at ha; subst a; trivial
  · exact checked7612
theorem derived7612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7612 := by
  apply localUnsat_implies_entails f7612 [c7610, c5427, c7556, c7555, c5222] c7612 unsat7612 (by rfl) a
  have h0 : Entails.eval a c7610 := derived7610 a h
  have h1 : Entails.eval a c5427 := h 5426 (by decide)
  have h2 : Entails.eval a c7556 := derived7556 a h
  have h3 : Entails.eval a c7555 := derived7555 a h
  have h4 : Entails.eval a c5222 := h 5221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7613 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7612, some c5138, some c5152, some c5137, some c5539, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7613 : lratChecker f7613 p7613 = .success := by decide +kernel
theorem unsat7613 : Unsatisfiable (PosFin 65) f7613 := by
  apply lratCheckerSound f7613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7613
  · intro a ha; simp [p7613] at ha; subst a; trivial
  · exact checked7613
theorem derived7613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7613 := by
  apply localUnsat_implies_entails f7613 [c7612, c5138, c5152, c5137, c5539] c7613 unsat7613 (by rfl) a
  have h0 : Entails.eval a c7612 := derived7612 a h
  have h1 : Entails.eval a c5138 := h 5137 (by decide)
  have h2 : Entails.eval a c5152 := h 5151 (by decide)
  have h3 : Entails.eval a c5137 := h 5136 (by decide)
  have h4 : Entails.eval a c5539 := h 5538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7614 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨45, by decide⟩, true), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7605, some c6703, some c6930, some c7241, some c6531, some c7611, some c7613, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7614 : lratChecker f7614 p7614 = .success := by decide +kernel
theorem unsat7614 : Unsatisfiable (PosFin 65) f7614 := by
  apply lratCheckerSound f7614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7614
  · intro a ha; simp [p7614] at ha; subst a; trivial
  · exact checked7614
theorem derived7614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7614 := by
  apply localUnsat_implies_entails f7614 [c7605, c6703, c6930, c7241, c6531, c7611, c7613] c7614 unsat7614 (by rfl) a
  have h0 : Entails.eval a c7605 := derived7605 a h
  have h1 : Entails.eval a c6703 := h 6702 (by decide)
  have h2 : Entails.eval a c6930 := h 6929 (by decide)
  have h3 : Entails.eval a c7241 := h 7240 (by decide)
  have h4 : Entails.eval a c6531 := h 6530 (by decide)
  have h5 : Entails.eval a c7611 := derived7611 a h
  have h6 : Entails.eval a c7613 := derived7613 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7615 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5155, some c5150, some c7609, some c7555, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7615 : lratChecker f7615 p7615 = .success := by decide +kernel
theorem unsat7615 : Unsatisfiable (PosFin 65) f7615 := by
  apply lratCheckerSound f7615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7615
  · intro a ha; simp [p7615] at ha; subst a; trivial
  · exact checked7615
theorem derived7615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7615 := by
  apply localUnsat_implies_entails f7615 [c5155, c5150, c7609, c7555] c7615 unsat7615 (by rfl) a
  have h0 : Entails.eval a c5155 := h 5154 (by decide)
  have h1 : Entails.eval a c5150 := h 5149 (by decide)
  have h2 : Entails.eval a c7609 := derived7609 a h
  have h3 : Entails.eval a c7555 := derived7555 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7616 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5427, some c5347, some c5248, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7616 : lratChecker f7616 p7616 = .success := by decide +kernel
theorem unsat7616 : Unsatisfiable (PosFin 65) f7616 := by
  apply lratCheckerSound f7616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7616
  · intro a ha; simp [p7616] at ha; subst a; trivial
  · exact checked7616
theorem derived7616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7616 := by
  apply localUnsat_implies_entails f7616 [c5427, c5347, c5248] c7616 unsat7616 (by rfl) a
  have h0 : Entails.eval a c5427 := h 5426 (by decide)
  have h1 : Entails.eval a c5347 := h 5346 (by decide)
  have h2 : Entails.eval a c5248 := h 5247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7617 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7605, some c6703, some c7241, some c7188, some c6930, some c7602, some c7614, some c6516, some c7615, some c7616, some c5221, some c5200, some c5255, some c7554, some c5711, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7617 : lratChecker f7617 p7617 = .success := by decide +kernel
theorem unsat7617 : Unsatisfiable (PosFin 65) f7617 := by
  apply lratCheckerSound f7617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7617
  · intro a ha; simp [p7617] at ha; subst a; trivial
  · exact checked7617
theorem derived7617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7617 := by
  apply localUnsat_implies_entails f7617 [c7605, c6703, c7241, c7188, c6930, c7602, c7614, c6516, c7615, c7616, c5221, c5200, c5255, c7554, c5711] c7617 unsat7617 (by rfl) a
  have h0 : Entails.eval a c7605 := derived7605 a h
  have h1 : Entails.eval a c6703 := h 6702 (by decide)
  have h2 : Entails.eval a c7241 := h 7240 (by decide)
  have h3 : Entails.eval a c7188 := h 7187 (by decide)
  have h4 : Entails.eval a c6930 := h 6929 (by decide)
  have h5 : Entails.eval a c7602 := derived7602 a h
  have h6 : Entails.eval a c7614 := derived7614 a h
  have h7 : Entails.eval a c6516 := h 6515 (by decide)
  have h8 : Entails.eval a c7615 := derived7615 a h
  have h9 : Entails.eval a c7616 := derived7616 a h
  have h10 : Entails.eval a c5221 := h 5220 (by decide)
  have h11 : Entails.eval a c5200 := h 5199 (by decide)
  have h12 : Entails.eval a c5255 := h 5254 (by decide)
  have h13 : Entails.eval a c7554 := derived7554 a h
  have h14 : Entails.eval a c5711 := h 5710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7618 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5221, some c5200, some c5255, some c7554, some c7570, some c5716, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7618 : lratChecker f7618 p7618 = .success := by decide +kernel
theorem unsat7618 : Unsatisfiable (PosFin 65) f7618 := by
  apply lratCheckerSound f7618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7618
  · intro a ha; simp [p7618] at ha; subst a; trivial
  · exact checked7618
theorem derived7618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7618 := by
  apply localUnsat_implies_entails f7618 [c5221, c5200, c5255, c7554, c7570, c5716] c7618 unsat7618 (by rfl) a
  have h0 : Entails.eval a c5221 := h 5220 (by decide)
  have h1 : Entails.eval a c5200 := h 5199 (by decide)
  have h2 : Entails.eval a c5255 := h 5254 (by decide)
  have h3 : Entails.eval a c7554 := derived7554 a h
  have h4 : Entails.eval a c7570 := derived7570 a h
  have h5 : Entails.eval a c5716 := h 5715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7619 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨17, by decide⟩, false), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5150, some c7571, some c7555, some c7608, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7619 : lratChecker f7619 p7619 = .success := by decide +kernel
theorem unsat7619 : Unsatisfiable (PosFin 65) f7619 := by
  apply lratCheckerSound f7619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7619
  · intro a ha; simp [p7619] at ha; subst a; trivial
  · exact checked7619
theorem derived7619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7619 := by
  apply localUnsat_implies_entails f7619 [c5150, c7571, c7555, c7608] c7619 unsat7619 (by rfl) a
  have h0 : Entails.eval a c5150 := h 5149 (by decide)
  have h1 : Entails.eval a c7571 := derived7571 a h
  have h2 : Entails.eval a c7555 := derived7555 a h
  have h3 : Entails.eval a c7608 := derived7608 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7620 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨39, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7605, some c7601, some c7471, some c6729, some c6703, some c7604, some c7241, some c6930, some c7188, some c7336, some c7131, some c7606, some c7617, some c7169, some c6525, some c7618, some c7616, some c7619, some c5160, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7620 : lratChecker f7620 p7620 = .success := by decide +kernel
theorem unsat7620 : Unsatisfiable (PosFin 65) f7620 := by
  apply lratCheckerSound f7620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7620
  · intro a ha; simp [p7620] at ha; subst a; trivial
  · exact checked7620
theorem derived7620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7620 := by
  apply localUnsat_implies_entails f7620 [c7605, c7601, c7471, c6729, c6703, c7604, c7241, c6930, c7188, c7336, c7131, c7606, c7617, c7169, c6525, c7618, c7616, c7619, c5160] c7620 unsat7620 (by rfl) a
  have h0 : Entails.eval a c7605 := derived7605 a h
  have h1 : Entails.eval a c7601 := derived7601 a h
  have h2 : Entails.eval a c7471 := h 7470 (by decide)
  have h3 : Entails.eval a c6729 := h 6728 (by decide)
  have h4 : Entails.eval a c6703 := h 6702 (by decide)
  have h5 : Entails.eval a c7604 := derived7604 a h
  have h6 : Entails.eval a c7241 := h 7240 (by decide)
  have h7 : Entails.eval a c6930 := h 6929 (by decide)
  have h8 : Entails.eval a c7188 := h 7187 (by decide)
  have h9 : Entails.eval a c7336 := h 7335 (by decide)
  have h10 : Entails.eval a c7131 := h 7130 (by decide)
  have h11 : Entails.eval a c7606 := derived7606 a h
  have h12 : Entails.eval a c7617 := derived7617 a h
  have h13 : Entails.eval a c7169 := h 7168 (by decide)
  have h14 : Entails.eval a c6525 := h 6524 (by decide)
  have h15 : Entails.eval a c7618 := derived7618 a h
  have h16 : Entails.eval a c7616 := derived7616 a h
  have h17 : Entails.eval a c7619 := derived7619 a h
  have h18 : Entails.eval a c5160 := h 5159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7621 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7241, some c6930, some c6813, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7621 : lratChecker f7621 p7621 = .success := by decide +kernel
theorem unsat7621 : Unsatisfiable (PosFin 65) f7621 := by
  apply lratCheckerSound f7621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7621
  · intro a ha; simp [p7621] at ha; subst a; trivial
  · exact checked7621
theorem derived7621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7621 := by
  apply localUnsat_implies_entails f7621 [c7241, c6930, c6813] c7621 unsat7621 (by rfl) a
  have h0 : Entails.eval a c7241 := h 7240 (by decide)
  have h1 : Entails.eval a c6930 := h 6929 (by decide)
  have h2 : Entails.eval a c6813 := h 6812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7622 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨37, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6664, some c6974, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7622 : lratChecker f7622 p7622 = .success := by decide +kernel
theorem unsat7622 : Unsatisfiable (PosFin 65) f7622 := by
  apply lratCheckerSound f7622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7622
  · intro a ha; simp [p7622] at ha; subst a; trivial
  · exact checked7622
theorem derived7622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7622 := by
  apply localUnsat_implies_entails f7622 [c6664, c6974] c7622 unsat7622 (by rfl) a
  have h0 : Entails.eval a c6664 := h 6663 (by decide)
  have h1 : Entails.eval a c6974 := h 6973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7623 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6379, some c6975, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7623 : lratChecker f7623 p7623 = .success := by decide +kernel
theorem unsat7623 : Unsatisfiable (PosFin 65) f7623 := by
  apply lratCheckerSound f7623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7623
  · intro a ha; simp [p7623] at ha; subst a; trivial
  · exact checked7623
theorem derived7623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7623 := by
  apply localUnsat_implies_entails f7623 [c6379, c6975] c7623 unsat7623 (by rfl) a
  have h0 : Entails.eval a c6379 := h 6378 (by decide)
  have h1 : Entails.eval a c6975 := h 6974 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7624 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7601, some c7605, some c7620, some c7621, some c7106, some c7431, some c7520, some c6993, some c6626, some c6795, some c6813, some c6314, some c7552, some c7622, some c7623, some c7442, some c6665, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7624 : lratChecker f7624 p7624 = .success := by decide +kernel
theorem unsat7624 : Unsatisfiable (PosFin 65) f7624 := by
  apply lratCheckerSound f7624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7624
  · intro a ha; simp [p7624] at ha; subst a; trivial
  · exact checked7624
theorem derived7624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7624 := by
  apply localUnsat_implies_entails f7624 [c7601, c7605, c7620, c7621, c7106, c7431, c7520, c6993, c6626, c6795, c6813, c6314, c7552, c7622, c7623, c7442, c6665] c7624 unsat7624 (by rfl) a
  have h0 : Entails.eval a c7601 := derived7601 a h
  have h1 : Entails.eval a c7605 := derived7605 a h
  have h2 : Entails.eval a c7620 := derived7620 a h
  have h3 : Entails.eval a c7621 := derived7621 a h
  have h4 : Entails.eval a c7106 := h 7105 (by decide)
  have h5 : Entails.eval a c7431 := h 7430 (by decide)
  have h6 : Entails.eval a c7520 := h 7519 (by decide)
  have h7 : Entails.eval a c6993 := h 6992 (by decide)
  have h8 : Entails.eval a c6626 := h 6625 (by decide)
  have h9 : Entails.eval a c6795 := h 6794 (by decide)
  have h10 : Entails.eval a c6813 := h 6812 (by decide)
  have h11 : Entails.eval a c6314 := h 6313 (by decide)
  have h12 : Entails.eval a c7552 := derived7552 a h
  have h13 : Entails.eval a c7622 := derived7622 a h
  have h14 : Entails.eval a c7623 := derived7623 a h
  have h15 : Entails.eval a c7442 := h 7441 (by decide)
  have h16 : Entails.eval a c6665 := h 6664 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7625 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨36, by decide⟩, true), (⟨43, by decide⟩, false), (⟨39, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7520, some c6795, some c7372, some c6813, some c6703, some c6613, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7625 : lratChecker f7625 p7625 = .success := by decide +kernel
theorem unsat7625 : Unsatisfiable (PosFin 65) f7625 := by
  apply lratCheckerSound f7625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7625
  · intro a ha; simp [p7625] at ha; subst a; trivial
  · exact checked7625
theorem derived7625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7625 := by
  apply localUnsat_implies_entails f7625 [c7520, c6795, c7372, c6813, c6703, c6613] c7625 unsat7625 (by rfl) a
  have h0 : Entails.eval a c7520 := h 7519 (by decide)
  have h1 : Entails.eval a c6795 := h 6794 (by decide)
  have h2 : Entails.eval a c7372 := h 7371 (by decide)
  have h3 : Entails.eval a c6813 := h 6812 (by decide)
  have h4 : Entails.eval a c6703 := h 6702 (by decide)
  have h5 : Entails.eval a c6613 := h 6612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7626 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6574, some c6613, some c6813, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7626 : lratChecker f7626 p7626 = .success := by decide +kernel
theorem unsat7626 : Unsatisfiable (PosFin 65) f7626 := by
  apply lratCheckerSound f7626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7626
  · intro a ha; simp [p7626] at ha; subst a; trivial
  · exact checked7626
theorem derived7626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7626 := by
  apply localUnsat_implies_entails f7626 [c6574, c6613, c6813] c7626 unsat7626 (by rfl) a
  have h0 : Entails.eval a c6574 := h 6573 (by decide)
  have h1 : Entails.eval a c6613 := h 6612 (by decide)
  have h2 : Entails.eval a c6813 := h 6812 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7627 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6813, some c6314, some c6402, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7627 : lratChecker f7627 p7627 = .success := by decide +kernel
theorem unsat7627 : Unsatisfiable (PosFin 65) f7627 := by
  apply lratCheckerSound f7627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7627
  · intro a ha; simp [p7627] at ha; subst a; trivial
  · exact checked7627
theorem derived7627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7627 := by
  apply localUnsat_implies_entails f7627 [c6813, c6314, c6402] c7627 unsat7627 (by rfl) a
  have h0 : Entails.eval a c6813 := h 6812 (by decide)
  have h1 : Entails.eval a c6314 := h 6313 (by decide)
  have h2 : Entails.eval a c6402 := h 6401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7628 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨43, by decide⟩, false), (⟨63, by decide⟩, false), (⟨39, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7625, some c7626, some c7627, some c6777, some c6795, some c6653, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p7628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7628 : lratChecker f7628 p7628 = .success := by decide +kernel
theorem unsat7628 : Unsatisfiable (PosFin 65) f7628 := by
  apply lratCheckerSound f7628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7628
  · intro a ha; simp [p7628] at ha; subst a; trivial
  · exact checked7628
theorem derived7628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7628 := by
  apply localUnsat_implies_entails f7628 [c7625, c7626, c7627, c6777, c6795, c6653] c7628 unsat7628 (by rfl) a
  have h0 : Entails.eval a c7625 := derived7625 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7627 := derived7627 a h
  have h3 : Entails.eval a c6777 := h 6776 (by decide)
  have h4 : Entails.eval a c6795 := h 6794 (by decide)
  have h5 : Entails.eval a c6653 := h 6652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7629 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨58, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7602, some c6462, some c6913, some c6461, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p7629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7629 : lratChecker f7629 p7629 = .success := by decide +kernel
theorem unsat7629 : Unsatisfiable (PosFin 65) f7629 := by
  apply lratCheckerSound f7629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7629
  · intro a ha; simp [p7629] at ha; subst a; trivial
  · exact checked7629
theorem derived7629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7629 := by
  apply localUnsat_implies_entails f7629 [c7602, c6462, c6913, c6461] c7629 unsat7629 (by rfl) a
  have h0 : Entails.eval a c7602 := derived7602 a h
  have h1 : Entails.eval a c6462 := h 6461 (by decide)
  have h2 : Entails.eval a c6913 := h 6912 (by decide)
  have h3 : Entails.eval a c6461 := h 6460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7630 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7624, some c7601, some c7628, some c6358, some c7106, some c7579, some c6402, some c6446, some c6459, some c7627, some c7195, some c7629, some c7169, some c6914, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7630 : lratChecker f7630 p7630 = .success := by decide +kernel
theorem unsat7630 : Unsatisfiable (PosFin 65) f7630 := by
  apply lratCheckerSound f7630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7630
  · intro a ha; simp [p7630] at ha; subst a; trivial
  · exact checked7630
theorem derived7630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7630 := by
  apply localUnsat_implies_entails f7630 [c7624, c7601, c7628, c6358, c7106, c7579, c6402, c6446, c6459, c7627, c7195, c7629, c7169, c6914] c7630 unsat7630 (by rfl) a
  have h0 : Entails.eval a c7624 := derived7624 a h
  have h1 : Entails.eval a c7601 := derived7601 a h
  have h2 : Entails.eval a c7628 := derived7628 a h
  have h3 : Entails.eval a c6358 := h 6357 (by decide)
  have h4 : Entails.eval a c7106 := h 7105 (by decide)
  have h5 : Entails.eval a c7579 := derived7579 a h
  have h6 : Entails.eval a c6402 := h 6401 (by decide)
  have h7 : Entails.eval a c6446 := h 6445 (by decide)
  have h8 : Entails.eval a c6459 := h 6458 (by decide)
  have h9 : Entails.eval a c7627 := derived7627 a h
  have h10 : Entails.eval a c7195 := h 7194 (by decide)
  have h11 : Entails.eval a c7629 := derived7629 a h
  have h12 : Entails.eval a c7169 := h 7168 (by decide)
  have h13 : Entails.eval a c6914 := h 6913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7631 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7169, some c6525, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7631 : lratChecker f7631 p7631 = .success := by decide +kernel
theorem unsat7631 : Unsatisfiable (PosFin 65) f7631 := by
  apply lratCheckerSound f7631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7631
  · intro a ha; simp [p7631] at ha; subst a; trivial
  · exact checked7631
theorem derived7631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7631 := by
  apply localUnsat_implies_entails f7631 [c7169, c6525] c7631 unsat7631 (by rfl) a
  have h0 : Entails.eval a c7169 := h 7168 (by decide)
  have h1 : Entails.eval a c6525 := h 6524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7632 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨41, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7624, some c7630, some c7379, some c7188, some c7601, some c7579, some c7631, some c7602, some c6462, some c7396, some c6461, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7632 : lratChecker f7632 p7632 = .success := by decide +kernel
theorem unsat7632 : Unsatisfiable (PosFin 65) f7632 := by
  apply lratCheckerSound f7632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7632
  · intro a ha; simp [p7632] at ha; subst a; trivial
  · exact checked7632
theorem derived7632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7632 := by
  apply localUnsat_implies_entails f7632 [c7624, c7630, c7379, c7188, c7601, c7579, c7631, c7602, c6462, c7396, c6461] c7632 unsat7632 (by rfl) a
  have h0 : Entails.eval a c7624 := derived7624 a h
  have h1 : Entails.eval a c7630 := derived7630 a h
  have h2 : Entails.eval a c7379 := h 7378 (by decide)
  have h3 : Entails.eval a c7188 := h 7187 (by decide)
  have h4 : Entails.eval a c7601 := derived7601 a h
  have h5 : Entails.eval a c7579 := derived7579 a h
  have h6 : Entails.eval a c7631 := derived7631 a h
  have h7 : Entails.eval a c7602 := derived7602 a h
  have h8 : Entails.eval a c6462 := h 6461 (by decide)
  have h9 : Entails.eval a c7396 := h 7395 (by decide)
  have h10 : Entails.eval a c6461 := h 6460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7633 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7630, some c7624, some c7601, some c7420, some c7422, some c7387, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7633 : lratChecker f7633 p7633 = .success := by decide +kernel
theorem unsat7633 : Unsatisfiable (PosFin 65) f7633 := by
  apply lratCheckerSound f7633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7633
  · intro a ha; simp [p7633] at ha; subst a; trivial
  · exact checked7633
theorem derived7633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7633 := by
  apply localUnsat_implies_entails f7633 [c7630, c7624, c7601, c7420, c7422, c7387] c7633 unsat7633 (by rfl) a
  have h0 : Entails.eval a c7630 := derived7630 a h
  have h1 : Entails.eval a c7624 := derived7624 a h
  have h2 : Entails.eval a c7601 := derived7601 a h
  have h3 : Entails.eval a c7420 := h 7419 (by decide)
  have h4 : Entails.eval a c7422 := h 7421 (by decide)
  have h5 : Entails.eval a c7387 := h 7386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7634 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨48, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6287, some c6653, some c6446, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7634 : lratChecker f7634 p7634 = .success := by decide +kernel
theorem unsat7634 : Unsatisfiable (PosFin 65) f7634 := by
  apply lratCheckerSound f7634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7634
  · intro a ha; simp [p7634] at ha; subst a; trivial
  · exact checked7634
theorem derived7634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7634 := by
  apply localUnsat_implies_entails f7634 [c6287, c6653, c6446] c7634 unsat7634 (by rfl) a
  have h0 : Entails.eval a c6287 := h 6286 (by decide)
  have h1 : Entails.eval a c6653 := h 6652 (by decide)
  have h2 : Entails.eval a c6446 := h 6445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7635 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7624, some c7630, some c6674, some c7379, some c6703, some c7634, some c6402, some c6446, some c7632, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7635 : lratChecker f7635 p7635 = .success := by decide +kernel
theorem unsat7635 : Unsatisfiable (PosFin 65) f7635 := by
  apply lratCheckerSound f7635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7635
  · intro a ha; simp [p7635] at ha; subst a; trivial
  · exact checked7635
theorem derived7635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7635 := by
  apply localUnsat_implies_entails f7635 [c7624, c7630, c6674, c7379, c6703, c7634, c6402, c6446, c7632] c7635 unsat7635 (by rfl) a
  have h0 : Entails.eval a c7624 := derived7624 a h
  have h1 : Entails.eval a c7630 := derived7630 a h
  have h2 : Entails.eval a c6674 := h 6673 (by decide)
  have h3 : Entails.eval a c7379 := h 7378 (by decide)
  have h4 : Entails.eval a c6703 := h 6702 (by decide)
  have h5 : Entails.eval a c7634 := derived7634 a h
  have h6 : Entails.eval a c6402 := h 6401 (by decide)
  have h7 : Entails.eval a c6446 := h 6445 (by decide)
  have h8 : Entails.eval a c7632 := derived7632 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7636 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7624, some c7630, some c7379, some c6674, some c6703, some c7634, some c7633, some c7604, some c6688, some c6685, some c7635, some c6510, some c6508, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p7636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7636 : lratChecker f7636 p7636 = .success := by decide +kernel
theorem unsat7636 : Unsatisfiable (PosFin 65) f7636 := by
  apply lratCheckerSound f7636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7636
  · intro a ha; simp [p7636] at ha; subst a; trivial
  · exact checked7636
theorem derived7636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7636 := by
  apply localUnsat_implies_entails f7636 [c7624, c7630, c7379, c6674, c6703, c7634, c7633, c7604, c6688, c6685, c7635, c6510, c6508] c7636 unsat7636 (by rfl) a
  have h0 : Entails.eval a c7624 := derived7624 a h
  have h1 : Entails.eval a c7630 := derived7630 a h
  have h2 : Entails.eval a c7379 := h 7378 (by decide)
  have h3 : Entails.eval a c6674 := h 6673 (by decide)
  have h4 : Entails.eval a c6703 := h 6702 (by decide)
  have h5 : Entails.eval a c7634 := derived7634 a h
  have h6 : Entails.eval a c7633 := derived7633 a h
  have h7 : Entails.eval a c7604 := derived7604 a h
  have h8 : Entails.eval a c6688 := h 6687 (by decide)
  have h9 : Entails.eval a c6685 := h 6684 (by decide)
  have h10 : Entails.eval a c7635 := derived7635 a h
  have h11 : Entails.eval a c6510 := h 6509 (by decide)
  have h12 : Entails.eval a c6508 := h 6507 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7637 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6688, some c6685, some c6295, some c6290, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7637 : lratChecker f7637 p7637 = .success := by decide +kernel
theorem unsat7637 : Unsatisfiable (PosFin 65) f7637 := by
  apply lratCheckerSound f7637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7637
  · intro a ha; simp [p7637] at ha; subst a; trivial
  · exact checked7637
theorem derived7637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7637 := by
  apply localUnsat_implies_entails f7637 [c6688, c6685, c6295, c6290] c7637 unsat7637 (by rfl) a
  have h0 : Entails.eval a c6688 := h 6687 (by decide)
  have h1 : Entails.eval a c6685 := h 6684 (by decide)
  have h2 : Entails.eval a c6295 := h 6294 (by decide)
  have h3 : Entails.eval a c6290 := h 6289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7638 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7420, some c7422, some c7390, some c7387, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7638 : lratChecker f7638 p7638 = .success := by decide +kernel
theorem unsat7638 : Unsatisfiable (PosFin 65) f7638 := by
  apply lratCheckerSound f7638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7638
  · intro a ha; simp [p7638] at ha; subst a; trivial
  · exact checked7638
theorem derived7638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7638 := by
  apply localUnsat_implies_entails f7638 [c7420, c7422, c7390, c7387] c7638 unsat7638 (by rfl) a
  have h0 : Entails.eval a c7420 := h 7419 (by decide)
  have h1 : Entails.eval a c7422 := h 7421 (by decide)
  have h2 : Entails.eval a c7390 := h 7389 (by decide)
  have h3 : Entails.eval a c7387 := h 7386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7639 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6507, some c6322, some c6924, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p7639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7639 : lratChecker f7639 p7639 = .success := by decide +kernel
theorem unsat7639 : Unsatisfiable (PosFin 65) f7639 := by
  apply lratCheckerSound f7639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7639
  · intro a ha; simp [p7639] at ha; subst a; trivial
  · exact checked7639
theorem derived7639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7639 := by
  apply localUnsat_implies_entails f7639 [c6507, c6322, c6924] c7639 unsat7639 (by rfl) a
  have h0 : Entails.eval a c6507 := h 6506 (by decide)
  have h1 : Entails.eval a c6322 := h 6321 (by decide)
  have h2 : Entails.eval a c6924 := h 6923 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7640 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7638, some c7637, some c6671, some c6673, some c7639, some c7398, some c7581, some c7038, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7640 : lratChecker f7640 p7640 = .success := by decide +kernel
theorem unsat7640 : Unsatisfiable (PosFin 65) f7640 := by
  apply lratCheckerSound f7640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7640
  · intro a ha; simp [p7640] at ha; subst a; trivial
  · exact checked7640
theorem derived7640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7640 := by
  apply localUnsat_implies_entails f7640 [c7638, c7637, c6671, c6673, c7639, c7398, c7581, c7038] c7640 unsat7640 (by rfl) a
  have h0 : Entails.eval a c7638 := derived7638 a h
  have h1 : Entails.eval a c7637 := derived7637 a h
  have h2 : Entails.eval a c6671 := h 6670 (by decide)
  have h3 : Entails.eval a c6673 := h 6672 (by decide)
  have h4 : Entails.eval a c7639 := derived7639 a h
  have h5 : Entails.eval a c7398 := h 7397 (by decide)
  have h6 : Entails.eval a c7581 := derived7581 a h
  have h7 : Entails.eval a c7038 := h 7037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7641 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7636, some c7640, some c7369, some c7370, some c7368, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7641 : lratChecker f7641 p7641 = .success := by decide +kernel
theorem unsat7641 : Unsatisfiable (PosFin 65) f7641 := by
  apply lratCheckerSound f7641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7641
  · intro a ha; simp [p7641] at ha; subst a; trivial
  · exact checked7641
theorem derived7641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7641 := by
  apply localUnsat_implies_entails f7641 [c7636, c7640, c7369, c7370, c7368] c7641 unsat7641 (by rfl) a
  have h0 : Entails.eval a c7636 := derived7636 a h
  have h1 : Entails.eval a c7640 := derived7640 a h
  have h2 : Entails.eval a c7369 := h 7368 (by decide)
  have h3 : Entails.eval a c7370 := h 7369 (by decide)
  have h4 : Entails.eval a c7368 := h 7367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7642 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨41, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6884, some c7452, some c6864, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7642 : lratChecker f7642 p7642 = .success := by decide +kernel
theorem unsat7642 : Unsatisfiable (PosFin 65) f7642 := by
  apply lratCheckerSound f7642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7642
  · intro a ha; simp [p7642] at ha; subst a; trivial
  · exact checked7642
theorem derived7642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7642 := by
  apply localUnsat_implies_entails f7642 [c6884, c7452, c6864] c7642 unsat7642 (by rfl) a
  have h0 : Entails.eval a c6884 := h 6883 (by decide)
  have h1 : Entails.eval a c7452 := h 7451 (by decide)
  have h2 : Entails.eval a c6864 := h 6863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7643 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨50, by decide⟩, true), (⟨17, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5191, some c5177, some c5338, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7643 : lratChecker f7643 p7643 = .success := by decide +kernel
theorem unsat7643 : Unsatisfiable (PosFin 65) f7643 := by
  apply lratCheckerSound f7643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7643
  · intro a ha; simp [p7643] at ha; subst a; trivial
  · exact checked7643
theorem derived7643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7643 := by
  apply localUnsat_implies_entails f7643 [c5191, c5177, c5338] c7643 unsat7643 (by rfl) a
  have h0 : Entails.eval a c5191 := h 5190 (by decide)
  have h1 : Entails.eval a c5177 := h 5176 (by decide)
  have h2 : Entails.eval a c5338 := h 5337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7644 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨56, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5213, some c5226, some c5421, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7644 : lratChecker f7644 p7644 = .success := by decide +kernel
theorem unsat7644 : Unsatisfiable (PosFin 65) f7644 := by
  apply lratCheckerSound f7644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7644
  · intro a ha; simp [p7644] at ha; subst a; trivial
  · exact checked7644
theorem derived7644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7644 := by
  apply localUnsat_implies_entails f7644 [c5213, c5226, c5421] c7644 unsat7644 (by rfl) a
  have h0 : Entails.eval a c5213 := h 5212 (by decide)
  have h1 : Entails.eval a c5226 := h 5225 (by decide)
  have h2 : Entails.eval a c5421 := h 5420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7645 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5711, some c5738, some c5525, some c5616, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p7645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7645 : lratChecker f7645 p7645 = .success := by decide +kernel
theorem unsat7645 : Unsatisfiable (PosFin 65) f7645 := by
  apply lratCheckerSound f7645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7645
  · intro a ha; simp [p7645] at ha; subst a; trivial
  · exact checked7645
theorem derived7645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7645 := by
  apply localUnsat_implies_entails f7645 [c5711, c5738, c5525, c5616] c7645 unsat7645 (by rfl) a
  have h0 : Entails.eval a c5711 := h 5710 (by decide)
  have h1 : Entails.eval a c5738 := h 5737 (by decide)
  have h2 : Entails.eval a c5525 := h 5524 (by decide)
  have h3 : Entails.eval a c5616 := h 5615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7646 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5191, some c5142, some c5183, some c7643, some c5329, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7646 : lratChecker f7646 p7646 = .success := by decide +kernel
theorem unsat7646 : Unsatisfiable (PosFin 65) f7646 := by
  apply lratCheckerSound f7646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7646
  · intro a ha; simp [p7646] at ha; subst a; trivial
  · exact checked7646
theorem derived7646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7646 := by
  apply localUnsat_implies_entails f7646 [c5191, c5142, c5183, c7643, c5329] c7646 unsat7646 (by rfl) a
  have h0 : Entails.eval a c5191 := h 5190 (by decide)
  have h1 : Entails.eval a c5142 := h 5141 (by decide)
  have h2 : Entails.eval a c5183 := h 5182 (by decide)
  have h3 : Entails.eval a c7643 := derived7643 a h
  have h4 : Entails.eval a c5329 := h 5328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7647 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨56, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5157, some c7644, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p7647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7647 : lratChecker f7647 p7647 = .success := by decide +kernel
theorem unsat7647 : Unsatisfiable (PosFin 65) f7647 := by
  apply lratCheckerSound f7647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7647
  · intro a ha; simp [p7647] at ha; subst a; trivial
  · exact checked7647
theorem derived7647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7647 := by
  apply localUnsat_implies_entails f7647 [c5157, c7644] c7647 unsat7647 (by rfl) a
  have h0 : Entails.eval a c5157 := h 5156 (by decide)
  have h1 : Entails.eval a c7644 := derived7644 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7648 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨20, by decide⟩, true), (⟨56, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7646, some c7645, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7648 : lratChecker f7648 p7648 = .success := by decide +kernel
theorem unsat7648 : Unsatisfiable (PosFin 65) f7648 := by
  apply lratCheckerSound f7648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7648
  · intro a ha; simp [p7648] at ha; subst a; trivial
  · exact checked7648
theorem derived7648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7648 := by
  apply localUnsat_implies_entails f7648 [c7646, c7645] c7648 unsat7648 (by rfl) a
  have h0 : Entails.eval a c7646 := derived7646 a h
  have h1 : Entails.eval a c7645 := derived7645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7649 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5531, some c5713, some c5168, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7649 : lratChecker f7649 p7649 = .success := by decide +kernel
theorem unsat7649 : Unsatisfiable (PosFin 65) f7649 := by
  apply lratCheckerSound f7649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7649
  · intro a ha; simp [p7649] at ha; subst a; trivial
  · exact checked7649
theorem derived7649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7649 := by
  apply localUnsat_implies_entails f7649 [c5531, c5713, c5168] c7649 unsat7649 (by rfl) a
  have h0 : Entails.eval a c5531 := h 5530 (by decide)
  have h1 : Entails.eval a c5713 := h 5712 (by decide)
  have h2 : Entails.eval a c5168 := h 5167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7650 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨39, by decide⟩, false), (⟨43, by decide⟩, true), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6853, some c7033, some c6752, some c6864, some c6335, some c7220, some c7647, some c7648, some c7333, some c7649, some c5191, some c5142, some c5181, some c5338, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p7650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7650 : lratChecker f7650 p7650 = .success := by decide +kernel
theorem unsat7650 : Unsatisfiable (PosFin 65) f7650 := by
  apply lratCheckerSound f7650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7650
  · intro a ha; simp [p7650] at ha; subst a; trivial
  · exact checked7650
theorem derived7650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7650 := by
  apply localUnsat_implies_entails f7650 [c6853, c7033, c6752, c6864, c6335, c7220, c7647, c7648, c7333, c7649, c5191, c5142, c5181, c5338] c7650 unsat7650 (by rfl) a
  have h0 : Entails.eval a c6853 := h 6852 (by decide)
  have h1 : Entails.eval a c7033 := h 7032 (by decide)
  have h2 : Entails.eval a c6752 := h 6751 (by decide)
  have h3 : Entails.eval a c6864 := h 6863 (by decide)
  have h4 : Entails.eval a c6335 := h 6334 (by decide)
  have h5 : Entails.eval a c7220 := h 7219 (by decide)
  have h6 : Entails.eval a c7647 := derived7647 a h
  have h7 : Entails.eval a c7648 := derived7648 a h
  have h8 : Entails.eval a c7333 := h 7332 (by decide)
  have h9 : Entails.eval a c7649 := derived7649 a h
  have h10 : Entails.eval a c5191 := h 5190 (by decide)
  have h11 : Entails.eval a c5142 := h 5141 (by decide)
  have h12 : Entails.eval a c5181 := h 5180 (by decide)
  have h13 : Entails.eval a c5338 := h 5337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7650

end CochromaticTwenty.Certificates.FixedCore0
