import MerLeanExperiment.Certificates.FixedCore1.Steps0600_0699

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6581 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6490, some c6540, some c6554, some c6573, some c6580, some c6475, some c6369, some c6518, some c6459, some c3681, some c6460, some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6581 : lratChecker f6581 p6581 = .success := by decide +kernel
theorem unsat6581 : Unsatisfiable (PosFin 65) f6581 := by
  apply lratCheckerSound f6581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6581
  · intro a ha; simp [p6581] at ha; subst a; trivial
  · exact checked6581
theorem derived6581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6581 := by
  apply localUnsat_implies_entails f6581 [c6227, c6490, c6540, c6554, c6573, c6580, c6475, c6369, c6518, c6459, c3681, c6460] c6581 unsat6581 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6540 := derived6540 a h
  have h3 : Entails.eval a c6554 := derived6554 a h
  have h4 : Entails.eval a c6573 := derived6573 a h
  have h5 : Entails.eval a c6580 := derived6580 a h
  have h6 : Entails.eval a c6475 := derived6475 a h
  have h7 : Entails.eval a c6369 := derived6369 a h
  have h8 : Entails.eval a c6518 := derived6518 a h
  have h9 : Entails.eval a c6459 := derived6459 a h
  have h10 : Entails.eval a c3681 := h 3680 (by decide)
  have h11 : Entails.eval a c6460 := derived6460 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6582 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5715, some c5718, some c5708, some c5709, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6582 : lratChecker f6582 p6582 = .success := by decide +kernel
theorem unsat6582 : Unsatisfiable (PosFin 65) f6582 := by
  apply lratCheckerSound f6582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6582
  · intro a ha; simp [p6582] at ha; subst a; trivial
  · exact checked6582
theorem derived6582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6582 := by
  apply localUnsat_implies_entails f6582 [c5715, c5718, c5708, c5709] c6582 unsat6582 (by rfl) a
  have h0 : Entails.eval a c5715 := h 5714 (by decide)
  have h1 : Entails.eval a c5718 := h 5717 (by decide)
  have h2 : Entails.eval a c5708 := h 5707 (by decide)
  have h3 : Entails.eval a c5709 := h 5708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6583 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5693, some c5084, some c5206, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6583 : lratChecker f6583 p6583 = .success := by decide +kernel
theorem unsat6583 : Unsatisfiable (PosFin 65) f6583 := by
  apply lratCheckerSound f6583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6583
  · intro a ha; simp [p6583] at ha; subst a; trivial
  · exact checked6583
theorem derived6583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6583 := by
  apply localUnsat_implies_entails f6583 [c5693, c5084, c5206] c6583 unsat6583 (by rfl) a
  have h0 : Entails.eval a c5693 := h 5692 (by decide)
  have h1 : Entails.eval a c5084 := h 5083 (by decide)
  have h2 : Entails.eval a c5206 := h 5205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6584 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6582, some c6583, some c5700, some c5565, some c5868, some c5206, some c5027, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6584 : lratChecker f6584 p6584 = .success := by decide +kernel
theorem unsat6584 : Unsatisfiable (PosFin 65) f6584 := by
  apply lratCheckerSound f6584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6584
  · intro a ha; simp [p6584] at ha; subst a; trivial
  · exact checked6584
theorem derived6584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6584 := by
  apply localUnsat_implies_entails f6584 [c6582, c6583, c5700, c5565, c5868, c5206, c5027] c6584 unsat6584 (by rfl) a
  have h0 : Entails.eval a c6582 := derived6582 a h
  have h1 : Entails.eval a c6583 := derived6583 a h
  have h2 : Entails.eval a c5700 := h 5699 (by decide)
  have h3 : Entails.eval a c5565 := h 5564 (by decide)
  have h4 : Entails.eval a c5868 := h 5867 (by decide)
  have h5 : Entails.eval a c5206 := h 5205 (by decide)
  have h6 : Entails.eval a c5027 := h 5026 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6585 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨63, by decide⟩, true), (⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4960, some c4956, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p6585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6585 : lratChecker f6585 p6585 = .success := by decide +kernel
theorem unsat6585 : Unsatisfiable (PosFin 65) f6585 := by
  apply lratCheckerSound f6585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6585
  · intro a ha; simp [p6585] at ha; subst a; trivial
  · exact checked6585
theorem derived6585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6585 := by
  apply localUnsat_implies_entails f6585 [c4960, c4956] c6585 unsat6585 (by rfl) a
  have h0 : Entails.eval a c4960 := h 4959 (by decide)
  have h1 : Entails.eval a c4956 := h 4955 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6586 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨47, by decide⟩, true), (⟨39, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4843, some c5488, some c4113, some c4860, some c6369, some c4484, some c3959, some c6585, some c3584, some c5160, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6586 : lratChecker f6586 p6586 = .success := by decide +kernel
theorem unsat6586 : Unsatisfiable (PosFin 65) f6586 := by
  apply lratCheckerSound f6586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6586
  · intro a ha; simp [p6586] at ha; subst a; trivial
  · exact checked6586
theorem derived6586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6586 := by
  apply localUnsat_implies_entails f6586 [c4843, c5488, c4113, c4860, c6369, c4484, c3959, c6585, c3584, c5160] c6586 unsat6586 (by rfl) a
  have h0 : Entails.eval a c4843 := h 4842 (by decide)
  have h1 : Entails.eval a c5488 := h 5487 (by decide)
  have h2 : Entails.eval a c4113 := h 4112 (by decide)
  have h3 : Entails.eval a c4860 := h 4859 (by decide)
  have h4 : Entails.eval a c6369 := derived6369 a h
  have h5 : Entails.eval a c4484 := h 4483 (by decide)
  have h6 : Entails.eval a c3959 := h 3958 (by decide)
  have h7 : Entails.eval a c6585 := derived6585 a h
  have h8 : Entails.eval a c3584 := h 3583 (by decide)
  have h9 : Entails.eval a c5160 := h 5159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6587 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨57, by decide⟩, true), (⟨56, by decide⟩, false), (⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4063, some c4064, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p6587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6587 : lratChecker f6587 p6587 = .success := by decide +kernel
theorem unsat6587 : Unsatisfiable (PosFin 65) f6587 := by
  apply lratCheckerSound f6587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6587
  · intro a ha; simp [p6587] at ha; subst a; trivial
  · exact checked6587
theorem derived6587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6587 := by
  apply localUnsat_implies_entails f6587 [c6581, c4063, c4064] c6587 unsat6587 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4063 := h 4062 (by decide)
  have h2 : Entails.eval a c4064 := h 4063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6588 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3617, some c4650, some c3541, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6588 : lratChecker f6588 p6588 = .success := by decide +kernel
theorem unsat6588 : Unsatisfiable (PosFin 65) f6588 := by
  apply lratCheckerSound f6588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6588
  · intro a ha; simp [p6588] at ha; subst a; trivial
  · exact checked6588
theorem derived6588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6588 := by
  apply localUnsat_implies_entails f6588 [c3617, c4650, c3541] c6588 unsat6588 (by rfl) a
  have h0 : Entails.eval a c3617 := h 3616 (by decide)
  have h1 : Entails.eval a c4650 := h 4649 (by decide)
  have h2 : Entails.eval a c3541 := h 3540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6589 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨63, by decide⟩, false), (⟨44, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨46, by decide⟩, true), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5871, some c5559, some c5585, some c5207, some c5219, some c5220, some c5208, some c4688, some c6587, some c4114, some c4539, some c6588, some c4594, some c4662, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6589 : lratChecker f6589 p6589 = .success := by decide +kernel
theorem unsat6589 : Unsatisfiable (PosFin 65) f6589 := by
  apply lratCheckerSound f6589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6589
  · intro a ha; simp [p6589] at ha; subst a; trivial
  · exact checked6589
theorem derived6589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6589 := by
  apply localUnsat_implies_entails f6589 [c5871, c5559, c5585, c5207, c5219, c5220, c5208, c4688, c6587, c4114, c4539, c6588, c4594, c4662] c6589 unsat6589 (by rfl) a
  have h0 : Entails.eval a c5871 := h 5870 (by decide)
  have h1 : Entails.eval a c5559 := h 5558 (by decide)
  have h2 : Entails.eval a c5585 := h 5584 (by decide)
  have h3 : Entails.eval a c5207 := h 5206 (by decide)
  have h4 : Entails.eval a c5219 := h 5218 (by decide)
  have h5 : Entails.eval a c5220 := h 5219 (by decide)
  have h6 : Entails.eval a c5208 := h 5207 (by decide)
  have h7 : Entails.eval a c4688 := h 4687 (by decide)
  have h8 : Entails.eval a c6587 := derived6587 a h
  have h9 : Entails.eval a c4114 := h 4113 (by decide)
  have h10 : Entails.eval a c4539 := h 4538 (by decide)
  have h11 : Entails.eval a c6588 := derived6588 a h
  have h12 : Entails.eval a c4594 := h 4593 (by decide)
  have h13 : Entails.eval a c4662 := h 4661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6590 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6582, some c6584, some c5697, some c5871, some c5559, some c5585, some c6586, some c6589, some c5234, some c5030, some c5238, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6590 : lratChecker f6590 p6590 = .success := by decide +kernel
theorem unsat6590 : Unsatisfiable (PosFin 65) f6590 := by
  apply lratCheckerSound f6590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6590
  · intro a ha; simp [p6590] at ha; subst a; trivial
  · exact checked6590
theorem derived6590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6590 := by
  apply localUnsat_implies_entails f6590 [c6582, c6584, c5697, c5871, c5559, c5585, c6586, c6589, c5234, c5030, c5238] c6590 unsat6590 (by rfl) a
  have h0 : Entails.eval a c6582 := derived6582 a h
  have h1 : Entails.eval a c6584 := derived6584 a h
  have h2 : Entails.eval a c5697 := h 5696 (by decide)
  have h3 : Entails.eval a c5871 := h 5870 (by decide)
  have h4 : Entails.eval a c5559 := h 5558 (by decide)
  have h5 : Entails.eval a c5585 := h 5584 (by decide)
  have h6 : Entails.eval a c6586 := derived6586 a h
  have h7 : Entails.eval a c6589 := derived6589 a h
  have h8 : Entails.eval a c5234 := h 5233 (by decide)
  have h9 : Entails.eval a c5030 := h 5029 (by decide)
  have h10 : Entails.eval a c5238 := h 5237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6591 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨50, by decide⟩, true), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3605, some c3606, some c3608, some c4653, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p6591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6591 : lratChecker f6591 p6591 = .success := by decide +kernel
theorem unsat6591 : Unsatisfiable (PosFin 65) f6591 := by
  apply lratCheckerSound f6591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6591
  · intro a ha; simp [p6591] at ha; subst a; trivial
  · exact checked6591
theorem derived6591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6591 := by
  apply localUnsat_implies_entails f6591 [c6581, c3605, c3606, c3608, c4653] c6591 unsat6591 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3605 := h 3604 (by decide)
  have h2 : Entails.eval a c3606 := h 3605 (by decide)
  have h3 : Entails.eval a c3608 := h 3607 (by decide)
  have h4 : Entails.eval a c4653 := h 4652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6592 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6582, some c5694, some c5556, some c5865, some c4835, some c5577, some c5482, some c4853, some c3822, some c6591, some c5142, some c5089, some c5055, some c5127, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6592 : lratChecker f6592 p6592 = .success := by decide +kernel
theorem unsat6592 : Unsatisfiable (PosFin 65) f6592 := by
  apply lratCheckerSound f6592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6592
  · intro a ha; simp [p6592] at ha; subst a; trivial
  · exact checked6592
theorem derived6592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6592 := by
  apply localUnsat_implies_entails f6592 [c6581, c6582, c5694, c5556, c5865, c4835, c5577, c5482, c4853, c3822, c6591, c5142, c5089, c5055, c5127] c6592 unsat6592 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6582 := derived6582 a h
  have h2 : Entails.eval a c5694 := h 5693 (by decide)
  have h3 : Entails.eval a c5556 := h 5555 (by decide)
  have h4 : Entails.eval a c5865 := h 5864 (by decide)
  have h5 : Entails.eval a c4835 := h 4834 (by decide)
  have h6 : Entails.eval a c5577 := h 5576 (by decide)
  have h7 : Entails.eval a c5482 := h 5481 (by decide)
  have h8 : Entails.eval a c4853 := h 4852 (by decide)
  have h9 : Entails.eval a c3822 := h 3821 (by decide)
  have h10 : Entails.eval a c6591 := derived6591 a h
  have h11 : Entails.eval a c5142 := h 5141 (by decide)
  have h12 : Entails.eval a c5089 := h 5088 (by decide)
  have h13 : Entails.eval a c5055 := h 5054 (by decide)
  have h14 : Entails.eval a c5127 := h 5126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6593 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨37, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5107, some c5083, some c5080, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6593 : lratChecker f6593 p6593 = .success := by decide +kernel
theorem unsat6593 : Unsatisfiable (PosFin 65) f6593 := by
  apply lratCheckerSound f6593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6593
  · intro a ha; simp [p6593] at ha; subst a; trivial
  · exact checked6593
theorem derived6593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6593 := by
  apply localUnsat_implies_entails f6593 [c6581, c5107, c5083, c5080] c6593 unsat6593 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5107 := h 5106 (by decide)
  have h2 : Entails.eval a c5083 := h 5082 (by decide)
  have h3 : Entails.eval a c5080 := h 5079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6594 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨37, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5086, some c5088, some c5091, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6594 : lratChecker f6594 p6594 = .success := by decide +kernel
theorem unsat6594 : Unsatisfiable (PosFin 65) f6594 := by
  apply lratCheckerSound f6594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6594
  · intro a ha; simp [p6594] at ha; subst a; trivial
  · exact checked6594
theorem derived6594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6594 := by
  apply localUnsat_implies_entails f6594 [c5086, c5088, c5091] c6594 unsat6594 (by rfl) a
  have h0 : Entails.eval a c5086 := h 5085 (by decide)
  have h1 : Entails.eval a c5088 := h 5087 (by decide)
  have h2 : Entails.eval a c5091 := h 5090 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6595 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨61, by decide⟩, true), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6582, some c6594, some c5700, some c5565, some c6302, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6595 : lratChecker f6595 p6595 = .success := by decide +kernel
theorem unsat6595 : Unsatisfiable (PosFin 65) f6595 := by
  apply lratCheckerSound f6595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6595
  · intro a ha; simp [p6595] at ha; subst a; trivial
  · exact checked6595
theorem derived6595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6595 := by
  apply localUnsat_implies_entails f6595 [c6582, c6594, c5700, c5565, c6302] c6595 unsat6595 (by rfl) a
  have h0 : Entails.eval a c6582 := derived6582 a h
  have h1 : Entails.eval a c6594 := derived6594 a h
  have h2 : Entails.eval a c5700 := h 5699 (by decide)
  have h3 : Entails.eval a c5565 := h 5564 (by decide)
  have h4 : Entails.eval a c6302 := derived6302 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6596 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨37, by decide⟩, true), (⟨61, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5700, some c4690, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6596 : lratChecker f6596 p6596 = .success := by decide +kernel
theorem unsat6596 : Unsatisfiable (PosFin 65) f6596 := by
  apply lratCheckerSound f6596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6596
  · intro a ha; simp [p6596] at ha; subst a; trivial
  · exact checked6596
theorem derived6596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6596 := by
  apply localUnsat_implies_entails f6596 [c5700, c4690] c6596 unsat6596 (by rfl) a
  have h0 : Entails.eval a c5700 := h 5699 (by decide)
  have h1 : Entails.eval a c4690 := h 4689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6597 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨61, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4674, some c5207, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p6597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6597 : lratChecker f6597 p6597 = .success := by decide +kernel
theorem unsat6597 : Unsatisfiable (PosFin 65) f6597 := by
  apply lratCheckerSound f6597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6597
  · intro a ha; simp [p6597] at ha; subst a; trivial
  · exact checked6597
theorem derived6597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6597 := by
  apply localUnsat_implies_entails f6597 [c4674, c5207] c6597 unsat6597 (by rfl) a
  have h0 : Entails.eval a c4674 := h 4673 (by decide)
  have h1 : Entails.eval a c5207 := h 5206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6598 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6582, some c6592, some c6590, some c6595, some c6596, some c6597, some c5697, some c5693, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6598 : lratChecker f6598 p6598 = .success := by decide +kernel
theorem unsat6598 : Unsatisfiable (PosFin 65) f6598 := by
  apply lratCheckerSound f6598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6598
  · intro a ha; simp [p6598] at ha; subst a; trivial
  · exact checked6598
theorem derived6598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6598 := by
  apply localUnsat_implies_entails f6598 [c6582, c6592, c6590, c6595, c6596, c6597, c5697, c5693] c6598 unsat6598 (by rfl) a
  have h0 : Entails.eval a c6582 := derived6582 a h
  have h1 : Entails.eval a c6592 := derived6592 a h
  have h2 : Entails.eval a c6590 := derived6590 a h
  have h3 : Entails.eval a c6595 := derived6595 a h
  have h4 : Entails.eval a c6596 := derived6596 a h
  have h5 : Entails.eval a c6597 := derived6597 a h
  have h6 : Entails.eval a c5697 := h 5696 (by decide)
  have h7 : Entails.eval a c5693 := h 5692 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6599 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3581, some c3864, some c3851, some c4855, some c4861, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p6599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6599 : lratChecker f6599 p6599 = .success := by decide +kernel
theorem unsat6599 : Unsatisfiable (PosFin 65) f6599 := by
  apply lratCheckerSound f6599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6599
  · intro a ha; simp [p6599] at ha; subst a; trivial
  · exact checked6599
theorem derived6599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6599 := by
  apply localUnsat_implies_entails f6599 [c3581, c3864, c3851, c4855, c4861] c6599 unsat6599 (by rfl) a
  have h0 : Entails.eval a c3581 := h 3580 (by decide)
  have h1 : Entails.eval a c3864 := h 3863 (by decide)
  have h2 : Entails.eval a c3851 := h 3850 (by decide)
  have h3 : Entails.eval a c4855 := h 4854 (by decide)
  have h4 : Entails.eval a c4861 := h 4860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6600 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6599, some c4288, some c4260, some c4048, some c4046, some c3867, some c3591, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6600 : lratChecker f6600 p6600 = .success := by decide +kernel
theorem unsat6600 : Unsatisfiable (PosFin 65) f6600 := by
  apply lratCheckerSound f6600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6600
  · intro a ha; simp [p6600] at ha; subst a; trivial
  · exact checked6600
theorem derived6600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6600 := by
  apply localUnsat_implies_entails f6600 [c6599, c4288, c4260, c4048, c4046, c3867, c3591] c6600 unsat6600 (by rfl) a
  have h0 : Entails.eval a c6599 := derived6599 a h
  have h1 : Entails.eval a c4288 := h 4287 (by decide)
  have h2 : Entails.eval a c4260 := h 4259 (by decide)
  have h3 : Entails.eval a c4048 := h 4047 (by decide)
  have h4 : Entails.eval a c4046 := h 4045 (by decide)
  have h5 : Entails.eval a c3867 := h 3866 (by decide)
  have h6 : Entails.eval a c3591 := h 3590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6601 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4790, some c4795, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p6601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6601 : lratChecker f6601 p6601 = .success := by decide +kernel
theorem unsat6601 : Unsatisfiable (PosFin 65) f6601 := by
  apply lratCheckerSound f6601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6601
  · intro a ha; simp [p6601] at ha; subst a; trivial
  · exact checked6601
theorem derived6601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6601 := by
  apply localUnsat_implies_entails f6601 [c4790, c4795] c6601 unsat6601 (by rfl) a
  have h0 : Entails.eval a c4790 := h 4789 (by decide)
  have h1 : Entails.eval a c4795 := h 4794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6602 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5754, some c5758, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6602 : lratChecker f6602 p6602 = .success := by decide +kernel
theorem unsat6602 : Unsatisfiable (PosFin 65) f6602 := by
  apply lratCheckerSound f6602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6602
  · intro a ha; simp [p6602] at ha; subst a; trivial
  · exact checked6602
theorem derived6602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6602 := by
  apply localUnsat_implies_entails f6602 [c5754, c5758] c6602 unsat6602 (by rfl) a
  have h0 : Entails.eval a c5754 := h 5753 (by decide)
  have h1 : Entails.eval a c5758 := h 5757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6603 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6598, some c6601, some c6602, some c6597, some c6600, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6603 : lratChecker f6603 p6603 = .success := by decide +kernel
theorem unsat6603 : Unsatisfiable (PosFin 65) f6603 := by
  apply lratCheckerSound f6603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6603
  · intro a ha; simp [p6603] at ha; subst a; trivial
  · exact checked6603
theorem derived6603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6603 := by
  apply localUnsat_implies_entails f6603 [c6598, c6601, c6602, c6597, c6600] c6603 unsat6603 (by rfl) a
  have h0 : Entails.eval a c6598 := derived6598 a h
  have h1 : Entails.eval a c6601 := derived6601 a h
  have h2 : Entails.eval a c6602 := derived6602 a h
  have h3 : Entails.eval a c6597 := derived6597 a h
  have h4 : Entails.eval a c6600 := derived6600 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6604 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4288, some c4260, some c4326, some c4056, some c4054, some c5848, some c3874, some c4605, some c3602, some c3945, some c3760, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6604 : lratChecker f6604 p6604 = .success := by decide +kernel
theorem unsat6604 : Unsatisfiable (PosFin 65) f6604 := by
  apply lratCheckerSound f6604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6604
  · intro a ha; simp [p6604] at ha; subst a; trivial
  · exact checked6604
theorem derived6604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6604 := by
  apply localUnsat_implies_entails f6604 [c6581, c4288, c4260, c4326, c4056, c4054, c5848, c3874, c4605, c3602, c3945, c3760] c6604 unsat6604 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4288 := h 4287 (by decide)
  have h2 : Entails.eval a c4260 := h 4259 (by decide)
  have h3 : Entails.eval a c4326 := h 4325 (by decide)
  have h4 : Entails.eval a c4056 := h 4055 (by decide)
  have h5 : Entails.eval a c4054 := h 4053 (by decide)
  have h6 : Entails.eval a c5848 := h 5847 (by decide)
  have h7 : Entails.eval a c3874 := h 3873 (by decide)
  have h8 : Entails.eval a c4605 := h 4604 (by decide)
  have h9 : Entails.eval a c3602 := h 3601 (by decide)
  have h10 : Entails.eval a c3945 := h 3944 (by decide)
  have h11 : Entails.eval a c3760 := h 3759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6605 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6603, some c6598, some c6604, some c3580, some c3864, some c3850, some c4859, some c4857, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6605 : lratChecker f6605 p6605 = .success := by decide +kernel
theorem unsat6605 : Unsatisfiable (PosFin 65) f6605 := by
  apply lratCheckerSound f6605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6605
  · intro a ha; simp [p6605] at ha; subst a; trivial
  · exact checked6605
theorem derived6605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6605 := by
  apply localUnsat_implies_entails f6605 [c6603, c6598, c6604, c3580, c3864, c3850, c4859, c4857] c6605 unsat6605 (by rfl) a
  have h0 : Entails.eval a c6603 := derived6603 a h
  have h1 : Entails.eval a c6598 := derived6598 a h
  have h2 : Entails.eval a c6604 := derived6604 a h
  have h3 : Entails.eval a c3580 := h 3579 (by decide)
  have h4 : Entails.eval a c3864 := h 3863 (by decide)
  have h5 : Entails.eval a c3850 := h 3849 (by decide)
  have h6 : Entails.eval a c4859 := h 4858 (by decide)
  have h7 : Entails.eval a c4857 := h 4856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6606 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6603, some c6605, some c5206, some c6589, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6606 : lratChecker f6606 p6606 = .success := by decide +kernel
theorem unsat6606 : Unsatisfiable (PosFin 65) f6606 := by
  apply lratCheckerSound f6606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6606
  · intro a ha; simp [p6606] at ha; subst a; trivial
  · exact checked6606
theorem derived6606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6606 := by
  apply localUnsat_implies_entails f6606 [c6603, c6605, c5206, c6589] c6606 unsat6606 (by rfl) a
  have h0 : Entails.eval a c6603 := derived6603 a h
  have h1 : Entails.eval a c6605 := derived6605 a h
  have h2 : Entails.eval a c5206 := h 5205 (by decide)
  have h3 : Entails.eval a c6589 := derived6589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6607 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6598, some c6606, some c6602, some c4790, some c4791, some c4794, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6607 : lratChecker f6607 p6607 = .success := by decide +kernel
theorem unsat6607 : Unsatisfiable (PosFin 65) f6607 := by
  apply lratCheckerSound f6607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6607
  · intro a ha; simp [p6607] at ha; subst a; trivial
  · exact checked6607
theorem derived6607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6607 := by
  apply localUnsat_implies_entails f6607 [c6598, c6606, c6602, c4790, c4791, c4794] c6607 unsat6607 (by rfl) a
  have h0 : Entails.eval a c6598 := derived6598 a h
  have h1 : Entails.eval a c6606 := derived6606 a h
  have h2 : Entails.eval a c6602 := derived6602 a h
  have h3 : Entails.eval a c4790 := h 4789 (by decide)
  have h4 : Entails.eval a c4791 := h 4790 (by decide)
  have h5 : Entails.eval a c4794 := h 4793 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6608 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4737, some c4793, some c4819, some c5470, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p6608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6608 : lratChecker f6608 p6608 = .success := by decide +kernel
theorem unsat6608 : Unsatisfiable (PosFin 65) f6608 := by
  apply lratCheckerSound f6608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6608
  · intro a ha; simp [p6608] at ha; subst a; trivial
  · exact checked6608
theorem derived6608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6608 := by
  apply localUnsat_implies_entails f6608 [c4737, c4793, c4819, c5470] c6608 unsat6608 (by rfl) a
  have h0 : Entails.eval a c4737 := h 4736 (by decide)
  have h1 : Entails.eval a c4793 := h 4792 (by decide)
  have h2 : Entails.eval a c4819 := h 4818 (by decide)
  have h3 : Entails.eval a c5470 := h 5469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6609 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5141, some c5144, some c5147, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6609 : lratChecker f6609 p6609 = .success := by decide +kernel
theorem unsat6609 : Unsatisfiable (PosFin 65) f6609 := by
  apply lratCheckerSound f6609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6609
  · intro a ha; simp [p6609] at ha; subst a; trivial
  · exact checked6609
theorem derived6609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6609 := by
  apply localUnsat_implies_entails f6609 [c5141, c5144, c5147] c6609 unsat6609 (by rfl) a
  have h0 : Entails.eval a c5141 := h 5140 (by decide)
  have h1 : Entails.eval a c5144 := h 5143 (by decide)
  have h2 : Entails.eval a c5147 := h 5146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6610 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6598, some c6608, some c6607, some c6609, some c4790, some c4791, some c4794, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6610 : lratChecker f6610 p6610 = .success := by decide +kernel
theorem unsat6610 : Unsatisfiable (PosFin 65) f6610 := by
  apply lratCheckerSound f6610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6610
  · intro a ha; simp [p6610] at ha; subst a; trivial
  · exact checked6610
theorem derived6610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6610 := by
  apply localUnsat_implies_entails f6610 [c6598, c6608, c6607, c6609, c4790, c4791, c4794] c6610 unsat6610 (by rfl) a
  have h0 : Entails.eval a c6598 := derived6598 a h
  have h1 : Entails.eval a c6608 := derived6608 a h
  have h2 : Entails.eval a c6607 := derived6607 a h
  have h3 : Entails.eval a c6609 := derived6609 a h
  have h4 : Entails.eval a c4790 := h 4789 (by decide)
  have h5 : Entails.eval a c4791 := h 4790 (by decide)
  have h6 : Entails.eval a c4794 := h 4793 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6611 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4733, some c4786, some c4817, some c5466, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p6611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6611 : lratChecker f6611 p6611 = .success := by decide +kernel
theorem unsat6611 : Unsatisfiable (PosFin 65) f6611 := by
  apply lratCheckerSound f6611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6611
  · intro a ha; simp [p6611] at ha; subst a; trivial
  · exact checked6611
theorem derived6611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6611 := by
  apply localUnsat_implies_entails f6611 [c4733, c4786, c4817, c5466] c6611 unsat6611 (by rfl) a
  have h0 : Entails.eval a c4733 := h 4732 (by decide)
  have h1 : Entails.eval a c4786 := h 4785 (by decide)
  have h2 : Entails.eval a c4817 := h 4816 (by decide)
  have h3 : Entails.eval a c5466 := h 5465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6612 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6598, some c6610, some c6611, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6612 : lratChecker f6612 p6612 = .success := by decide +kernel
theorem unsat6612 : Unsatisfiable (PosFin 65) f6612 := by
  apply lratCheckerSound f6612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6612
  · intro a ha; simp [p6612] at ha; subst a; trivial
  · exact checked6612
theorem derived6612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6612 := by
  apply localUnsat_implies_entails f6612 [c6598, c6610, c6611] c6612 unsat6612 (by rfl) a
  have h0 : Entails.eval a c6598 := derived6598 a h
  have h1 : Entails.eval a c6610 := derived6610 a h
  have h2 : Entails.eval a c6611 := derived6611 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6613 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨63, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5142, some c5140, some c5145, some c6087, some c3436, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6613 : lratChecker f6613 p6613 = .success := by decide +kernel
theorem unsat6613 : Unsatisfiable (PosFin 65) f6613 := by
  apply lratCheckerSound f6613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6613
  · intro a ha; simp [p6613] at ha; subst a; trivial
  · exact checked6613
theorem derived6613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6613 := by
  apply localUnsat_implies_entails f6613 [c6581, c5142, c5140, c5145, c6087, c3436] c6613 unsat6613 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5142 := h 5141 (by decide)
  have h2 : Entails.eval a c5140 := h 5139 (by decide)
  have h3 : Entails.eval a c5145 := h 5144 (by decide)
  have h4 : Entails.eval a c6087 := derived6087 a h
  have h5 : Entails.eval a c3436 := h 3435 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6614 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨54, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2695, some c2807, some c2810, some c3008, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6614 : lratChecker f6614 p6614 = .success := by decide +kernel
theorem unsat6614 : Unsatisfiable (PosFin 65) f6614 := by
  apply lratCheckerSound f6614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6614
  · intro a ha; simp [p6614] at ha; subst a; trivial
  · exact checked6614
theorem derived6614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6614 := by
  apply localUnsat_implies_entails f6614 [c6581, c2695, c2807, c2810, c3008] c6614 unsat6614 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2695 := h 2694 (by decide)
  have h2 : Entails.eval a c2807 := h 2806 (by decide)
  have h3 : Entails.eval a c2810 := h 2809 (by decide)
  have h4 : Entails.eval a c3008 := h 3007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6615 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, true), (⟨57, by decide⟩, false), (⟨61, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3223, some c3245, some c2763, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6615 : lratChecker f6615 p6615 = .success := by decide +kernel
theorem unsat6615 : Unsatisfiable (PosFin 65) f6615 := by
  apply lratCheckerSound f6615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6615
  · intro a ha; simp [p6615] at ha; subst a; trivial
  · exact checked6615
theorem derived6615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6615 := by
  apply localUnsat_implies_entails f6615 [c3223, c3245, c2763] c6615 unsat6615 (by rfl) a
  have h0 : Entails.eval a c3223 := h 3222 (by decide)
  have h1 : Entails.eval a c3245 := h 3244 (by decide)
  have h2 : Entails.eval a c2763 := h 2762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6616 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6612, some c4876, some c4897, some c5865, some c3865, some c5532, some c5283, some c6477, some c4114, some c4219, some c4150, some c4211, some c3996, some c3472, some c3477, some c3982, some c6614, some c6615, some c2686, some c2724, some c2733, some c3008, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked6616 : lratChecker f6616 p6616 = .success := by decide +kernel
theorem unsat6616 : Unsatisfiable (PosFin 65) f6616 := by
  apply lratCheckerSound f6616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6616
  · intro a ha; simp [p6616] at ha; subst a; trivial
  · exact checked6616
theorem derived6616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6616 := by
  apply localUnsat_implies_entails f6616 [c6581, c6612, c4876, c4897, c5865, c3865, c5532, c5283, c6477, c4114, c4219, c4150, c4211, c3996, c3472, c3477, c3982, c6614, c6615, c2686, c2724, c2733, c3008] c6616 unsat6616 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6612 := derived6612 a h
  have h2 : Entails.eval a c4876 := h 4875 (by decide)
  have h3 : Entails.eval a c4897 := h 4896 (by decide)
  have h4 : Entails.eval a c5865 := h 5864 (by decide)
  have h5 : Entails.eval a c3865 := h 3864 (by decide)
  have h6 : Entails.eval a c5532 := h 5531 (by decide)
  have h7 : Entails.eval a c5283 := h 5282 (by decide)
  have h8 : Entails.eval a c6477 := derived6477 a h
  have h9 : Entails.eval a c4114 := h 4113 (by decide)
  have h10 : Entails.eval a c4219 := h 4218 (by decide)
  have h11 : Entails.eval a c4150 := h 4149 (by decide)
  have h12 : Entails.eval a c4211 := h 4210 (by decide)
  have h13 : Entails.eval a c3996 := h 3995 (by decide)
  have h14 : Entails.eval a c3472 := h 3471 (by decide)
  have h15 : Entails.eval a c3477 := h 3476 (by decide)
  have h16 : Entails.eval a c3982 := h 3981 (by decide)
  have h17 : Entails.eval a c6614 := derived6614 a h
  have h18 : Entails.eval a c6615 := derived6615 a h
  have h19 : Entails.eval a c2686 := h 2685 (by decide)
  have h20 : Entails.eval a c2724 := h 2723 (by decide)
  have h21 : Entails.eval a c2733 := h 2732 (by decide)
  have h22 : Entails.eval a c3008 := h 3007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6617 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨54, by decide⟩, true), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨36, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2686, some c2724, some c2733, some c3008, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6617 : lratChecker f6617 p6617 = .success := by decide +kernel
theorem unsat6617 : Unsatisfiable (PosFin 65) f6617 := by
  apply lratCheckerSound f6617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6617
  · intro a ha; simp [p6617] at ha; subst a; trivial
  · exact checked6617
theorem derived6617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6617 := by
  apply localUnsat_implies_entails f6617 [c6581, c2686, c2724, c2733, c3008] c6617 unsat6617 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2686 := h 2685 (by decide)
  have h2 : Entails.eval a c2724 := h 2723 (by decide)
  have h3 : Entails.eval a c2733 := h 2732 (by decide)
  have h4 : Entails.eval a c3008 := h 3007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6618 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6612, some c4876, some c4897, some c5625, some c3764, some c5865, some c3506, some c3797, some c3865, some c5650, some c5532, some c5283, some c6477, some c6613, some c6616, some c4260, some c4242, some c4093, some c3941, some c6614, some c6617, some c3224, some c3244, some c2763, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked6618 : lratChecker f6618 p6618 = .success := by decide +kernel
theorem unsat6618 : Unsatisfiable (PosFin 65) f6618 := by
  apply lratCheckerSound f6618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6618
  · intro a ha; simp [p6618] at ha; subst a; trivial
  · exact checked6618
theorem derived6618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6618 := by
  apply localUnsat_implies_entails f6618 [c6581, c6612, c4876, c4897, c5625, c3764, c5865, c3506, c3797, c3865, c5650, c5532, c5283, c6477, c6613, c6616, c4260, c4242, c4093, c3941, c6614, c6617, c3224, c3244, c2763] c6618 unsat6618 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6612 := derived6612 a h
  have h2 : Entails.eval a c4876 := h 4875 (by decide)
  have h3 : Entails.eval a c4897 := h 4896 (by decide)
  have h4 : Entails.eval a c5625 := h 5624 (by decide)
  have h5 : Entails.eval a c3764 := h 3763 (by decide)
  have h6 : Entails.eval a c5865 := h 5864 (by decide)
  have h7 : Entails.eval a c3506 := h 3505 (by decide)
  have h8 : Entails.eval a c3797 := h 3796 (by decide)
  have h9 : Entails.eval a c3865 := h 3864 (by decide)
  have h10 : Entails.eval a c5650 := h 5649 (by decide)
  have h11 : Entails.eval a c5532 := h 5531 (by decide)
  have h12 : Entails.eval a c5283 := h 5282 (by decide)
  have h13 : Entails.eval a c6477 := derived6477 a h
  have h14 : Entails.eval a c6613 := derived6613 a h
  have h15 : Entails.eval a c6616 := derived6616 a h
  have h16 : Entails.eval a c4260 := h 4259 (by decide)
  have h17 : Entails.eval a c4242 := h 4241 (by decide)
  have h18 : Entails.eval a c4093 := h 4092 (by decide)
  have h19 : Entails.eval a c3941 := h 3940 (by decide)
  have h20 : Entails.eval a c6614 := derived6614 a h
  have h21 : Entails.eval a c6617 := derived6617 a h
  have h22 : Entails.eval a c3224 := h 3223 (by decide)
  have h23 : Entails.eval a c3244 := h 3243 (by decide)
  have h24 : Entails.eval a c2763 := h 2762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6619 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨39, by decide⟩, false), (⟨55, by decide⟩, false), (⟨61, by decide⟩, false), (⟨57, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3226, some c3251, some c2760, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p6619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6619 : lratChecker f6619 p6619 = .success := by decide +kernel
theorem unsat6619 : Unsatisfiable (PosFin 65) f6619 := by
  apply lratCheckerSound f6619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6619
  · intro a ha; simp [p6619] at ha; subst a; trivial
  · exact checked6619
theorem derived6619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6619 := by
  apply localUnsat_implies_entails f6619 [c3226, c3251, c2760] c6619 unsat6619 (by rfl) a
  have h0 : Entails.eval a c3226 := h 3225 (by decide)
  have h1 : Entails.eval a c3251 := h 3250 (by decide)
  have h2 : Entails.eval a c2760 := h 2759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6620 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨61, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5424, some c2696, some c2806, some c2808, some c3004, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6620 : lratChecker f6620 p6620 = .success := by decide +kernel
theorem unsat6620 : Unsatisfiable (PosFin 65) f6620 := by
  apply lratCheckerSound f6620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6620
  · intro a ha; simp [p6620] at ha; subst a; trivial
  · exact checked6620
theorem derived6620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6620 := by
  apply localUnsat_implies_entails f6620 [c5424, c2696, c2806, c2808, c3004] c6620 unsat6620 (by rfl) a
  have h0 : Entails.eval a c5424 := h 5423 (by decide)
  have h1 : Entails.eval a c2696 := h 2695 (by decide)
  have h2 : Entails.eval a c2806 := h 2805 (by decide)
  have h3 : Entails.eval a c2808 := h 2807 (by decide)
  have h4 : Entails.eval a c3004 := h 3003 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6621 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6618, some c6612, some c4194, some c4186, some c4181, some c4193, some c5624, some c5756, some c3803, some c5144, some c4028, some c4172, some c3509, some c4152, some c3828, some c5864, some c5645, some c3938, some c4019, some c4169, some c5424, some c5881, some c6620, some c6619, some c2687, some c2723, some c2732, some c3004, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked6621 : lratChecker f6621 p6621 = .success := by decide +kernel
theorem unsat6621 : Unsatisfiable (PosFin 65) f6621 := by
  apply lratCheckerSound f6621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6621
  · intro a ha; simp [p6621] at ha; subst a; trivial
  · exact checked6621
theorem derived6621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6621 := by
  apply localUnsat_implies_entails f6621 [c6581, c6618, c6612, c4194, c4186, c4181, c4193, c5624, c5756, c3803, c5144, c4028, c4172, c3509, c4152, c3828, c5864, c5645, c3938, c4019, c4169, c5424, c5881, c6620, c6619, c2687, c2723, c2732, c3004] c6621 unsat6621 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6618 := derived6618 a h
  have h2 : Entails.eval a c6612 := derived6612 a h
  have h3 : Entails.eval a c4194 := h 4193 (by decide)
  have h4 : Entails.eval a c4186 := h 4185 (by decide)
  have h5 : Entails.eval a c4181 := h 4180 (by decide)
  have h6 : Entails.eval a c4193 := h 4192 (by decide)
  have h7 : Entails.eval a c5624 := h 5623 (by decide)
  have h8 : Entails.eval a c5756 := h 5755 (by decide)
  have h9 : Entails.eval a c3803 := h 3802 (by decide)
  have h10 : Entails.eval a c5144 := h 5143 (by decide)
  have h11 : Entails.eval a c4028 := h 4027 (by decide)
  have h12 : Entails.eval a c4172 := h 4171 (by decide)
  have h13 : Entails.eval a c3509 := h 3508 (by decide)
  have h14 : Entails.eval a c4152 := h 4151 (by decide)
  have h15 : Entails.eval a c3828 := h 3827 (by decide)
  have h16 : Entails.eval a c5864 := h 5863 (by decide)
  have h17 : Entails.eval a c5645 := h 5644 (by decide)
  have h18 : Entails.eval a c3938 := h 3937 (by decide)
  have h19 : Entails.eval a c4019 := h 4018 (by decide)
  have h20 : Entails.eval a c4169 := h 4168 (by decide)
  have h21 : Entails.eval a c5424 := h 5423 (by decide)
  have h22 : Entails.eval a c5881 := derived5881 a h
  have h23 : Entails.eval a c6620 := derived6620 a h
  have h24 : Entails.eval a c6619 := derived6619 a h
  have h25 : Entails.eval a c2687 := h 2686 (by decide)
  have h26 : Entails.eval a c2723 := h 2722 (by decide)
  have h27 : Entails.eval a c2732 := h 2731 (by decide)
  have h28 : Entails.eval a c3004 := h 3003 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6622 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨36, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4902, some c4901, some c4900, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6622 : lratChecker f6622 p6622 = .success := by decide +kernel
theorem unsat6622 : Unsatisfiable (PosFin 65) f6622 := by
  apply lratCheckerSound f6622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6622
  · intro a ha; simp [p6622] at ha; subst a; trivial
  · exact checked6622
theorem derived6622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6622 := by
  apply localUnsat_implies_entails f6622 [c4902, c4901, c4900] c6622 unsat6622 (by rfl) a
  have h0 : Entails.eval a c4902 := h 4901 (by decide)
  have h1 : Entails.eval a c4901 := h 4900 (by decide)
  have h2 : Entails.eval a c4900 := h 4899 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6623 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨55, by decide⟩, false), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2687, some c2723, some c2732, some c3002, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6623 : lratChecker f6623 p6623 = .success := by decide +kernel
theorem unsat6623 : Unsatisfiable (PosFin 65) f6623 := by
  apply lratCheckerSound f6623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6623
  · intro a ha; simp [p6623] at ha; subst a; trivial
  · exact checked6623
theorem derived6623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6623 := by
  apply localUnsat_implies_entails f6623 [c2687, c2723, c2732, c3002] c6623 unsat6623 (by rfl) a
  have h0 : Entails.eval a c2687 := h 2686 (by decide)
  have h1 : Entails.eval a c2723 := h 2722 (by decide)
  have h2 : Entails.eval a c2732 := h 2731 (by decide)
  have h3 : Entails.eval a c3002 := h 3001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6624 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6612, some c6618, some c6622, some c6621, some c3426, some c3425, some c5902, some c5627, some c4878, some c5144, some c3983, some c3509, some c3477, some c3464, some c3828, some c3465, some c5864, some c4404, some c3982, some c4209, some c5533, some c3475, some c6623, some c6619, some c2696, some c2806, some c2808, some c3002, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked6624 : lratChecker f6624 p6624 = .success := by decide +kernel
theorem unsat6624 : Unsatisfiable (PosFin 65) f6624 := by
  apply lratCheckerSound f6624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6624
  · intro a ha; simp [p6624] at ha; subst a; trivial
  · exact checked6624
theorem derived6624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6624 := by
  apply localUnsat_implies_entails f6624 [c6581, c6612, c6618, c6622, c6621, c3426, c3425, c5902, c5627, c4878, c5144, c3983, c3509, c3477, c3464, c3828, c3465, c5864, c4404, c3982, c4209, c5533, c3475, c6623, c6619, c2696, c2806, c2808, c3002] c6624 unsat6624 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6612 := derived6612 a h
  have h2 : Entails.eval a c6618 := derived6618 a h
  have h3 : Entails.eval a c6622 := derived6622 a h
  have h4 : Entails.eval a c6621 := derived6621 a h
  have h5 : Entails.eval a c3426 := h 3425 (by decide)
  have h6 : Entails.eval a c3425 := h 3424 (by decide)
  have h7 : Entails.eval a c5902 := derived5902 a h
  have h8 : Entails.eval a c5627 := h 5626 (by decide)
  have h9 : Entails.eval a c4878 := h 4877 (by decide)
  have h10 : Entails.eval a c5144 := h 5143 (by decide)
  have h11 : Entails.eval a c3983 := h 3982 (by decide)
  have h12 : Entails.eval a c3509 := h 3508 (by decide)
  have h13 : Entails.eval a c3477 := h 3476 (by decide)
  have h14 : Entails.eval a c3464 := h 3463 (by decide)
  have h15 : Entails.eval a c3828 := h 3827 (by decide)
  have h16 : Entails.eval a c3465 := h 3464 (by decide)
  have h17 : Entails.eval a c5864 := h 5863 (by decide)
  have h18 : Entails.eval a c4404 := h 4403 (by decide)
  have h19 : Entails.eval a c3982 := h 3981 (by decide)
  have h20 : Entails.eval a c4209 := h 4208 (by decide)
  have h21 : Entails.eval a c5533 := h 5532 (by decide)
  have h22 : Entails.eval a c3475 := h 3474 (by decide)
  have h23 : Entails.eval a c6623 := derived6623 a h
  have h24 : Entails.eval a c6619 := derived6619 a h
  have h25 : Entails.eval a c2696 := h 2695 (by decide)
  have h26 : Entails.eval a c2806 := h 2805 (by decide)
  have h27 : Entails.eval a c2808 := h 2807 (by decide)
  have h28 : Entails.eval a c3002 := h 3001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6625 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6612, some c6618, some c6622, some c6624, some c3768, some c6434, some c3766, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6625 : lratChecker f6625 p6625 = .success := by decide +kernel
theorem unsat6625 : Unsatisfiable (PosFin 65) f6625 := by
  apply lratCheckerSound f6625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6625
  · intro a ha; simp [p6625] at ha; subst a; trivial
  · exact checked6625
theorem derived6625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6625 := by
  apply localUnsat_implies_entails f6625 [c6612, c6618, c6622, c6624, c3768, c6434, c3766] c6625 unsat6625 (by rfl) a
  have h0 : Entails.eval a c6612 := derived6612 a h
  have h1 : Entails.eval a c6618 := derived6618 a h
  have h2 : Entails.eval a c6622 := derived6622 a h
  have h3 : Entails.eval a c6624 := derived6624 a h
  have h4 : Entails.eval a c3768 := h 3767 (by decide)
  have h5 : Entails.eval a c6434 := derived6434 a h
  have h6 : Entails.eval a c3766 := h 3765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6626 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6625, some c6582, some c5697, some c5871, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6626 : lratChecker f6626 p6626 = .success := by decide +kernel
theorem unsat6626 : Unsatisfiable (PosFin 65) f6626 := by
  apply lratCheckerSound f6626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6626
  · intro a ha; simp [p6626] at ha; subst a; trivial
  · exact checked6626
theorem derived6626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6626 := by
  apply localUnsat_implies_entails f6626 [c6625, c6582, c5697, c5871] c6626 unsat6626 (by rfl) a
  have h0 : Entails.eval a c6625 := derived6625 a h
  have h1 : Entails.eval a c6582 := derived6582 a h
  have h2 : Entails.eval a c5697 := h 5696 (by decide)
  have h3 : Entails.eval a c5871 := h 5870 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6627 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5693, some c5864, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6627 : lratChecker f6627 p6627 = .success := by decide +kernel
theorem unsat6627 : Unsatisfiable (PosFin 65) f6627 := by
  apply lratCheckerSound f6627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6627
  · intro a ha; simp [p6627] at ha; subst a; trivial
  · exact checked6627
theorem derived6627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6627 := by
  apply localUnsat_implies_entails f6627 [c5693, c5864] c6627 unsat6627 (by rfl) a
  have h0 : Entails.eval a c5693 := h 5692 (by decide)
  have h1 : Entails.eval a c5864 := h 5863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6628 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6625, some c6582, some c6612, some c6622, some c6626, some c6627, some c6584, some c5700, some c5880, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6628 : lratChecker f6628 p6628 = .success := by decide +kernel
theorem unsat6628 : Unsatisfiable (PosFin 65) f6628 := by
  apply lratCheckerSound f6628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6628
  · intro a ha; simp [p6628] at ha; subst a; trivial
  · exact checked6628
theorem derived6628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6628 := by
  apply localUnsat_implies_entails f6628 [c6625, c6582, c6612, c6622, c6626, c6627, c6584, c5700, c5880] c6628 unsat6628 (by rfl) a
  have h0 : Entails.eval a c6625 := derived6625 a h
  have h1 : Entails.eval a c6582 := derived6582 a h
  have h2 : Entails.eval a c6612 := derived6612 a h
  have h3 : Entails.eval a c6622 := derived6622 a h
  have h4 : Entails.eval a c6626 := derived6626 a h
  have h5 : Entails.eval a c6627 := derived6627 a h
  have h6 : Entails.eval a c6584 := derived6584 a h
  have h7 : Entails.eval a c5700 := h 5699 (by decide)
  have h8 : Entails.eval a c5880 := h 5879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6629 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6612, some c6625, some c6582, some c6628, some c4897, some c5694, some c5865, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6629 : lratChecker f6629 p6629 = .success := by decide +kernel
theorem unsat6629 : Unsatisfiable (PosFin 65) f6629 := by
  apply lratCheckerSound f6629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6629
  · intro a ha; simp [p6629] at ha; subst a; trivial
  · exact checked6629
theorem derived6629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6629 := by
  apply localUnsat_implies_entails f6629 [c6612, c6625, c6582, c6628, c4897, c5694, c5865] c6629 unsat6629 (by rfl) a
  have h0 : Entails.eval a c6612 := derived6612 a h
  have h1 : Entails.eval a c6625 := derived6625 a h
  have h2 : Entails.eval a c6582 := derived6582 a h
  have h3 : Entails.eval a c6628 := derived6628 a h
  have h4 : Entails.eval a c4897 := h 4896 (by decide)
  have h5 : Entails.eval a c5694 := h 5693 (by decide)
  have h6 : Entails.eval a c5865 := h 5864 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6630 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, true), (⟨40, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5142, some c5087, some c5239, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6630 : lratChecker f6630 p6630 = .success := by decide +kernel
theorem unsat6630 : Unsatisfiable (PosFin 65) f6630 := by
  apply lratCheckerSound f6630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6630
  · intro a ha; simp [p6630] at ha; subst a; trivial
  · exact checked6630
theorem derived6630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6630 := by
  apply localUnsat_implies_entails f6630 [c5142, c5087, c5239] c6630 unsat6630 (by rfl) a
  have h0 : Entails.eval a c5142 := h 5141 (by decide)
  have h1 : Entails.eval a c5087 := h 5086 (by decide)
  have h2 : Entails.eval a c5239 := h 5238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6631 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨44, by decide⟩, true), (⟨36, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4670, some c4671, some c4673, some c4680, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p6631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6631 : lratChecker f6631 p6631 = .success := by decide +kernel
theorem unsat6631 : Unsatisfiable (PosFin 65) f6631 := by
  apply lratCheckerSound f6631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6631
  · intro a ha; simp [p6631] at ha; subst a; trivial
  · exact checked6631
theorem derived6631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6631 := by
  apply localUnsat_implies_entails f6631 [c6581, c4670, c4671, c4673, c4680] c6631 unsat6631 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4670 := h 4669 (by decide)
  have h2 : Entails.eval a c4671 := h 4670 (by decide)
  have h3 : Entails.eval a c4673 := h 4672 (by decide)
  have h4 : Entails.eval a c4680 := h 4679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6632 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6629, some c5710, some c5694, some c5865, some c4898, some c4836, some c6630, some c6631, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6632 : lratChecker f6632 p6632 = .success := by decide +kernel
theorem unsat6632 : Unsatisfiable (PosFin 65) f6632 := by
  apply lratCheckerSound f6632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6632
  · intro a ha; simp [p6632] at ha; subst a; trivial
  · exact checked6632
theorem derived6632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6632 := by
  apply localUnsat_implies_entails f6632 [c6629, c5710, c5694, c5865, c4898, c4836, c6630, c6631] c6632 unsat6632 (by rfl) a
  have h0 : Entails.eval a c6629 := derived6629 a h
  have h1 : Entails.eval a c5710 := h 5709 (by decide)
  have h2 : Entails.eval a c5694 := h 5693 (by decide)
  have h3 : Entails.eval a c5865 := h 5864 (by decide)
  have h4 : Entails.eval a c4898 := h 4897 (by decide)
  have h5 : Entails.eval a c4836 := h 4835 (by decide)
  have h6 : Entails.eval a c6630 := derived6630 a h
  have h7 : Entails.eval a c6631 := derived6631 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6633 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5220, some c5225, some c5206, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6633 : lratChecker f6633 p6633 = .success := by decide +kernel
theorem unsat6633 : Unsatisfiable (PosFin 65) f6633 := by
  apply lratCheckerSound f6633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6633
  · intro a ha; simp [p6633] at ha; subst a; trivial
  · exact checked6633
theorem derived6633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6633 := by
  apply localUnsat_implies_entails f6633 [c5220, c5225, c5206] c6633 unsat6633 (by rfl) a
  have h0 : Entails.eval a c5220 := h 5219 (by decide)
  have h1 : Entails.eval a c5225 := h 5224 (by decide)
  have h2 : Entails.eval a c5206 := h 5205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6634 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6632, some c5715, some c5718, some c5709, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6634 : lratChecker f6634 p6634 = .success := by decide +kernel
theorem unsat6634 : Unsatisfiable (PosFin 65) f6634 := by
  apply lratCheckerSound f6634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6634
  · intro a ha; simp [p6634] at ha; subst a; trivial
  · exact checked6634
theorem derived6634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6634 := by
  apply localUnsat_implies_entails f6634 [c6632, c5715, c5718, c5709] c6634 unsat6634 (by rfl) a
  have h0 : Entails.eval a c6632 := derived6632 a h
  have h1 : Entails.eval a c5715 := h 5714 (by decide)
  have h2 : Entails.eval a c5718 := h 5717 (by decide)
  have h3 : Entails.eval a c5709 := h 5708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6635 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨46, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5201, some c5211, some c5204, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p6635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6635 : lratChecker f6635 p6635 = .success := by decide +kernel
theorem unsat6635 : Unsatisfiable (PosFin 65) f6635 := by
  apply lratCheckerSound f6635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6635
  · intro a ha; simp [p6635] at ha; subst a; trivial
  · exact checked6635
theorem derived6635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6635 := by
  apply localUnsat_implies_entails f6635 [c6581, c5201, c5211, c5204] c6635 unsat6635 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5201 := h 5200 (by decide)
  have h2 : Entails.eval a c5211 := h 5210 (by decide)
  have h3 : Entails.eval a c5204 := h 5203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6636 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨46, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6633, some c6635, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6636 : lratChecker f6636 p6636 = .success := by decide +kernel
theorem unsat6636 : Unsatisfiable (PosFin 65) f6636 := by
  apply lratCheckerSound f6636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6636
  · intro a ha; simp [p6636] at ha; subst a; trivial
  · exact checked6636
theorem derived6636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6636 := by
  apply localUnsat_implies_entails f6636 [c6633, c6635] c6636 unsat6636 (by rfl) a
  have h0 : Entails.eval a c6633 := derived6633 a h
  have h1 : Entails.eval a c6635 := derived6635 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6637 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6632, some c5697, some c5700, some c5693, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6637 : lratChecker f6637 p6637 = .success := by decide +kernel
theorem unsat6637 : Unsatisfiable (PosFin 65) f6637 := by
  apply lratCheckerSound f6637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6637
  · intro a ha; simp [p6637] at ha; subst a; trivial
  · exact checked6637
theorem derived6637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6637 := by
  apply localUnsat_implies_entails f6637 [c6632, c5697, c5700, c5693] c6637 unsat6637 (by rfl) a
  have h0 : Entails.eval a c6632 := derived6632 a h
  have h1 : Entails.eval a c5697 := h 5696 (by decide)
  have h2 : Entails.eval a c5700 := h 5699 (by decide)
  have h3 : Entails.eval a c5693 := h 5692 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6638 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6629, some c6632, some c6634, some c6637, some c6636, some c6593, some c5090, some c5871, some c5244, some c5559, some c5239, some c5037, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6638 : lratChecker f6638 p6638 = .success := by decide +kernel
theorem unsat6638 : Unsatisfiable (PosFin 65) f6638 := by
  apply lratCheckerSound f6638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6638
  · intro a ha; simp [p6638] at ha; subst a; trivial
  · exact checked6638
theorem derived6638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6638 := by
  apply localUnsat_implies_entails f6638 [c6629, c6632, c6634, c6637, c6636, c6593, c5090, c5871, c5244, c5559, c5239, c5037] c6638 unsat6638 (by rfl) a
  have h0 : Entails.eval a c6629 := derived6629 a h
  have h1 : Entails.eval a c6632 := derived6632 a h
  have h2 : Entails.eval a c6634 := derived6634 a h
  have h3 : Entails.eval a c6637 := derived6637 a h
  have h4 : Entails.eval a c6636 := derived6636 a h
  have h5 : Entails.eval a c6593 := derived6593 a h
  have h6 : Entails.eval a c5090 := h 5089 (by decide)
  have h7 : Entails.eval a c5871 := h 5870 (by decide)
  have h8 : Entails.eval a c5244 := h 5243 (by decide)
  have h9 : Entails.eval a c5559 := h 5558 (by decide)
  have h10 : Entails.eval a c5239 := h 5238 (by decide)
  have h11 : Entails.eval a c5037 := h 5036 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6639 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6629, some c5871, some c5244, some c5559, some c5239, some c5037, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6639 : lratChecker f6639 p6639 = .success := by decide +kernel
theorem unsat6639 : Unsatisfiable (PosFin 65) f6639 := by
  apply lratCheckerSound f6639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6639
  · intro a ha; simp [p6639] at ha; subst a; trivial
  · exact checked6639
theorem derived6639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6639 := by
  apply localUnsat_implies_entails f6639 [c6629, c5871, c5244, c5559, c5239, c5037] c6639 unsat6639 (by rfl) a
  have h0 : Entails.eval a c6629 := derived6629 a h
  have h1 : Entails.eval a c5871 := h 5870 (by decide)
  have h2 : Entails.eval a c5244 := h 5243 (by decide)
  have h3 : Entails.eval a c5559 := h 5558 (by decide)
  have h4 : Entails.eval a c5239 := h 5238 (by decide)
  have h5 : Entails.eval a c5037 := h 5036 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6640 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5878, some c5864, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6640 : lratChecker f6640 p6640 = .success := by decide +kernel
theorem unsat6640 : Unsatisfiable (PosFin 65) f6640 := by
  apply lratCheckerSound f6640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6640
  · intro a ha; simp [p6640] at ha; subst a; trivial
  · exact checked6640
theorem derived6640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6640 := by
  apply localUnsat_implies_entails f6640 [c5878, c5864] c6640 unsat6640 (by rfl) a
  have h0 : Entails.eval a c5878 := h 5877 (by decide)
  have h1 : Entails.eval a c5864 := h 5863 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6641 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6639, some c6629, some c6640, some c5233, some c5228, some c5236, some c4908, some c4843, some c5565, some c5002, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6641 : lratChecker f6641 p6641 = .success := by decide +kernel
theorem unsat6641 : Unsatisfiable (PosFin 65) f6641 := by
  apply lratCheckerSound f6641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6641
  · intro a ha; simp [p6641] at ha; subst a; trivial
  · exact checked6641
theorem derived6641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6641 := by
  apply localUnsat_implies_entails f6641 [c6581, c6639, c6629, c6640, c5233, c5228, c5236, c4908, c4843, c5565, c5002] c6641 unsat6641 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6639 := derived6639 a h
  have h2 : Entails.eval a c6629 := derived6629 a h
  have h3 : Entails.eval a c6640 := derived6640 a h
  have h4 : Entails.eval a c5233 := h 5232 (by decide)
  have h5 : Entails.eval a c5228 := h 5227 (by decide)
  have h6 : Entails.eval a c5236 := h 5235 (by decide)
  have h7 : Entails.eval a c4908 := h 4907 (by decide)
  have h8 : Entails.eval a c4843 := h 4842 (by decide)
  have h9 : Entails.eval a c5565 := h 5564 (by decide)
  have h10 : Entails.eval a c5002 := h 5001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6642 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6638, some c6629, some c6639, some c6641, some c5865, some c5556, some c4898, some c5229, some c5236, some c4787, some c5002, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6642 : lratChecker f6642 p6642 = .success := by decide +kernel
theorem unsat6642 : Unsatisfiable (PosFin 65) f6642 := by
  apply lratCheckerSound f6642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6642
  · intro a ha; simp [p6642] at ha; subst a; trivial
  · exact checked6642
theorem derived6642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6642 := by
  apply localUnsat_implies_entails f6642 [c6581, c6638, c6629, c6639, c6641, c5865, c5556, c4898, c5229, c5236, c4787, c5002] c6642 unsat6642 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6638 := derived6638 a h
  have h2 : Entails.eval a c6629 := derived6629 a h
  have h3 : Entails.eval a c6639 := derived6639 a h
  have h4 : Entails.eval a c6641 := derived6641 a h
  have h5 : Entails.eval a c5865 := h 5864 (by decide)
  have h6 : Entails.eval a c5556 := h 5555 (by decide)
  have h7 : Entails.eval a c4898 := h 4897 (by decide)
  have h8 : Entails.eval a c5229 := h 5228 (by decide)
  have h9 : Entails.eval a c5236 := h 5235 (by decide)
  have h10 : Entails.eval a c4787 := h 4786 (by decide)
  have h11 : Entails.eval a c5002 := h 5001 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6643 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5229, some c5236, some c4894, some c5138, some c4834, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6643 : lratChecker f6643 p6643 = .success := by decide +kernel
theorem unsat6643 : Unsatisfiable (PosFin 65) f6643 := by
  apply lratCheckerSound f6643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6643
  · intro a ha; simp [p6643] at ha; subst a; trivial
  · exact checked6643
theorem derived6643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6643 := by
  apply localUnsat_implies_entails f6643 [c6581, c5229, c5236, c4894, c5138, c4834] c6643 unsat6643 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5229 := h 5228 (by decide)
  have h2 : Entails.eval a c5236 := h 5235 (by decide)
  have h3 : Entails.eval a c4894 := h 4893 (by decide)
  have h4 : Entails.eval a c5138 := h 5137 (by decide)
  have h5 : Entails.eval a c4834 := h 4833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6644 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5620, some c5138, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6644 : lratChecker f6644 p6644 = .success := by decide +kernel
theorem unsat6644 : Unsatisfiable (PosFin 65) f6644 := by
  apply lratCheckerSound f6644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6644
  · intro a ha; simp [p6644] at ha; subst a; trivial
  · exact checked6644
theorem derived6644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6644 := by
  apply localUnsat_implies_entails f6644 [c6581, c5620, c5138] c6644 unsat6644 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5620 := h 5619 (by decide)
  have h2 : Entails.eval a c5138 := h 5137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6645 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨48, by decide⟩, true), (⟨52, by decide⟩, false), (⟨46, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5751, some c5618, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6645 : lratChecker f6645 p6645 = .success := by decide +kernel
theorem unsat6645 : Unsatisfiable (PosFin 65) f6645 := by
  apply lratCheckerSound f6645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6645
  · intro a ha; simp [p6645] at ha; subst a; trivial
  · exact checked6645
theorem derived6645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6645 := by
  apply localUnsat_implies_entails f6645 [c5751, c5618] c6645 unsat6645 (by rfl) a
  have h0 : Entails.eval a c5751 := h 5750 (by decide)
  have h1 : Entails.eval a c5618 := h 5617 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6646 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨46, by decide⟩, false), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6643, some c6645, some c6644, some c4180, some c5884, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6646 : lratChecker f6646 p6646 = .success := by decide +kernel
theorem unsat6646 : Unsatisfiable (PosFin 65) f6646 := by
  apply lratCheckerSound f6646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6646
  · intro a ha; simp [p6646] at ha; subst a; trivial
  · exact checked6646
theorem derived6646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6646 := by
  apply localUnsat_implies_entails f6646 [c6643, c6645, c6644, c4180, c5884] c6646 unsat6646 (by rfl) a
  have h0 : Entails.eval a c6643 := derived6643 a h
  have h1 : Entails.eval a c6645 := derived6645 a h
  have h2 : Entails.eval a c6644 := derived6644 a h
  have h3 : Entails.eval a c4180 := h 4179 (by decide)
  have h4 : Entails.eval a c5884 := derived5884 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6647 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6638, some c6629, some c6642, some c6646, some c5758, some c5631, some c5242, some c5244, some c5239, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6647 : lratChecker f6647 p6647 = .success := by decide +kernel
theorem unsat6647 : Unsatisfiable (PosFin 65) f6647 := by
  apply lratCheckerSound f6647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6647
  · intro a ha; simp [p6647] at ha; subst a; trivial
  · exact checked6647
theorem derived6647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6647 := by
  apply localUnsat_implies_entails f6647 [c6638, c6629, c6642, c6646, c5758, c5631, c5242, c5244, c5239] c6647 unsat6647 (by rfl) a
  have h0 : Entails.eval a c6638 := derived6638 a h
  have h1 : Entails.eval a c6629 := derived6629 a h
  have h2 : Entails.eval a c6642 := derived6642 a h
  have h3 : Entails.eval a c6646 := derived6646 a h
  have h4 : Entails.eval a c5758 := h 5757 (by decide)
  have h5 : Entails.eval a c5631 := h 5630 (by decide)
  have h6 : Entails.eval a c5242 := h 5241 (by decide)
  have h7 : Entails.eval a c5244 := h 5243 (by decide)
  have h8 : Entails.eval a c5239 := h 5238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6648 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6647, some c6638, some c6629, some c4288, some c4186, some c5242, some c5244, some c5239, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6648 : lratChecker f6648 p6648 = .success := by decide +kernel
theorem unsat6648 : Unsatisfiable (PosFin 65) f6648 := by
  apply lratCheckerSound f6648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6648
  · intro a ha; simp [p6648] at ha; subst a; trivial
  · exact checked6648
theorem derived6648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6648 := by
  apply localUnsat_implies_entails f6648 [c6647, c6638, c6629, c4288, c4186, c5242, c5244, c5239] c6648 unsat6648 (by rfl) a
  have h0 : Entails.eval a c6647 := derived6647 a h
  have h1 : Entails.eval a c6638 := derived6638 a h
  have h2 : Entails.eval a c6629 := derived6629 a h
  have h3 : Entails.eval a c4288 := h 4287 (by decide)
  have h4 : Entails.eval a c4186 := h 4185 (by decide)
  have h5 : Entails.eval a c5242 := h 5241 (by decide)
  have h6 : Entails.eval a c5244 := h 5243 (by decide)
  have h7 : Entails.eval a c5239 := h 5238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6649 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5229, some c5236, some c4894, some c5138, some c4782, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6649 : lratChecker f6649 p6649 = .success := by decide +kernel
theorem unsat6649 : Unsatisfiable (PosFin 65) f6649 := by
  apply lratCheckerSound f6649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6649
  · intro a ha; simp [p6649] at ha; subst a; trivial
  · exact checked6649
theorem derived6649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6649 := by
  apply localUnsat_implies_entails f6649 [c6581, c5229, c5236, c4894, c5138, c4782] c6649 unsat6649 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5229 := h 5228 (by decide)
  have h2 : Entails.eval a c5236 := h 5235 (by decide)
  have h3 : Entails.eval a c4894 := h 4893 (by decide)
  have h4 : Entails.eval a c5138 := h 5137 (by decide)
  have h5 : Entails.eval a c4782 := h 4781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6650 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5618, some c5620, some c5628, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6650 : lratChecker f6650 p6650 = .success := by decide +kernel
theorem unsat6650 : Unsatisfiable (PosFin 65) f6650 := by
  apply lratCheckerSound f6650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6650
  · intro a ha; simp [p6650] at ha; subst a; trivial
  · exact checked6650
theorem derived6650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6650 := by
  apply localUnsat_implies_entails f6650 [c5618, c5620, c5628] c6650 unsat6650 (by rfl) a
  have h0 : Entails.eval a c5618 := h 5617 (by decide)
  have h1 : Entails.eval a c5620 := h 5619 (by decide)
  have h2 : Entails.eval a c5628 := h 5627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6651 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c5146, some c5145, some c5134, some c5138, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p6651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6651 : lratChecker f6651 p6651 = .success := by decide +kernel
theorem unsat6651 : Unsatisfiable (PosFin 65) f6651 := by
  apply lratCheckerSound f6651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6651
  · intro a ha; simp [p6651] at ha; subst a; trivial
  · exact checked6651
theorem derived6651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6651 := by
  apply localUnsat_implies_entails f6651 [c6581, c5146, c5145, c5134, c5138] c6651 unsat6651 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c5146 := h 5145 (by decide)
  have h2 : Entails.eval a c5145 := h 5144 (by decide)
  have h3 : Entails.eval a c5134 := h 5133 (by decide)
  have h4 : Entails.eval a c5138 := h 5137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6652 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, true), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6649, some c6650, some c6651, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6652 : lratChecker f6652 p6652 = .success := by decide +kernel
theorem unsat6652 : Unsatisfiable (PosFin 65) f6652 := by
  apply lratCheckerSound f6652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6652
  · intro a ha; simp [p6652] at ha; subst a; trivial
  · exact checked6652
theorem derived6652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6652 := by
  apply localUnsat_implies_entails f6652 [c6649, c6650, c6651] c6652 unsat6652 (by rfl) a
  have h0 : Entails.eval a c6649 := derived6649 a h
  have h1 : Entails.eval a c6650 := derived6650 a h
  have h2 : Entails.eval a c6651 := derived6651 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6653 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6638, some c6629, some c6648, some c6652, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6653 : lratChecker f6653 p6653 = .success := by decide +kernel
theorem unsat6653 : Unsatisfiable (PosFin 65) f6653 := by
  apply lratCheckerSound f6653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6653
  · intro a ha; simp [p6653] at ha; subst a; trivial
  · exact checked6653
theorem derived6653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6653 := by
  apply localUnsat_implies_entails f6653 [c6638, c6629, c6648, c6652] c6653 unsat6653 (by rfl) a
  have h0 : Entails.eval a c6638 := derived6638 a h
  have h1 : Entails.eval a c6629 := derived6629 a h
  have h2 : Entails.eval a c6648 := derived6648 a h
  have h3 : Entails.eval a c6652 := derived6652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6654 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4176, some c4211, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6654 : lratChecker f6654 p6654 = .success := by decide +kernel
theorem unsat6654 : Unsatisfiable (PosFin 65) f6654 := by
  apply lratCheckerSound f6654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6654
  · intro a ha; simp [p6654] at ha; subst a; trivial
  · exact checked6654
theorem derived6654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6654 := by
  apply localUnsat_implies_entails f6654 [c6581, c4176, c4211] c6654 unsat6654 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4176 := h 4175 (by decide)
  have h2 : Entails.eval a c4211 := h 4210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6655 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5751, some c4039, some c4206, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6655 : lratChecker f6655 p6655 = .success := by decide +kernel
theorem unsat6655 : Unsatisfiable (PosFin 65) f6655 := by
  apply lratCheckerSound f6655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6655
  · intro a ha; simp [p6655] at ha; subst a; trivial
  · exact checked6655
theorem derived6655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6655 := by
  apply localUnsat_implies_entails f6655 [c5751, c4039, c4206] c6655 unsat6655 (by rfl) a
  have h0 : Entails.eval a c5751 := h 5750 (by decide)
  have h1 : Entails.eval a c4039 := h 4038 (by decide)
  have h2 : Entails.eval a c4206 := h 4205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6656 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6654, some c4180, some c5884, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6656 : lratChecker f6656 p6656 = .success := by decide +kernel
theorem unsat6656 : Unsatisfiable (PosFin 65) f6656 := by
  apply lratCheckerSound f6656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6656
  · intro a ha; simp [p6656] at ha; subst a; trivial
  · exact checked6656
theorem derived6656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6656 := by
  apply localUnsat_implies_entails f6656 [c6654, c4180, c5884] c6656 unsat6656 (by rfl) a
  have h0 : Entails.eval a c6654 := derived6654 a h
  have h1 : Entails.eval a c4180 := h 4179 (by decide)
  have h2 : Entails.eval a c5884 := derived5884 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6657 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4212, some c4018, some c3805, some c5468, some c3680, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p6657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6657 : lratChecker f6657 p6657 = .success := by decide +kernel
theorem unsat6657 : Unsatisfiable (PosFin 65) f6657 := by
  apply lratCheckerSound f6657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6657
  · intro a ha; simp [p6657] at ha; subst a; trivial
  · exact checked6657
theorem derived6657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6657 := by
  apply localUnsat_implies_entails f6657 [c4212, c4018, c3805, c5468, c3680] c6657 unsat6657 (by rfl) a
  have h0 : Entails.eval a c4212 := h 4211 (by decide)
  have h1 : Entails.eval a c4018 := h 4017 (by decide)
  have h2 : Entails.eval a c3805 := h 3804 (by decide)
  have h3 : Entails.eval a c5468 := h 5467 (by decide)
  have h4 : Entails.eval a c3680 := h 3679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6658 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c6655, some c6656, some c6657, some c4211, some c4156, some c3932, some c4574, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6658 : lratChecker f6658 p6658 = .success := by decide +kernel
theorem unsat6658 : Unsatisfiable (PosFin 65) f6658 := by
  apply lratCheckerSound f6658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6658
  · intro a ha; simp [p6658] at ha; subst a; trivial
  · exact checked6658
theorem derived6658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6658 := by
  apply localUnsat_implies_entails f6658 [c6581, c6655, c6656, c6657, c4211, c4156, c3932, c4574] c6658 unsat6658 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c6655 := derived6655 a h
  have h2 : Entails.eval a c6656 := derived6656 a h
  have h3 : Entails.eval a c6657 := derived6657 a h
  have h4 : Entails.eval a c4211 := h 4210 (by decide)
  have h5 : Entails.eval a c4156 := h 4155 (by decide)
  have h6 : Entails.eval a c3932 := h 3931 (by decide)
  have h7 : Entails.eval a c4574 := h 4573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6659 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4785, some c4894, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p6659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6659 : lratChecker f6659 p6659 = .success := by decide +kernel
theorem unsat6659 : Unsatisfiable (PosFin 65) f6659 := by
  apply lratCheckerSound f6659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6659
  · intro a ha; simp [p6659] at ha; subst a; trivial
  · exact checked6659
theorem derived6659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6659 := by
  apply localUnsat_implies_entails f6659 [c6581, c4785, c4894] c6659 unsat6659 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4785 := h 4784 (by decide)
  have h2 : Entails.eval a c4894 := h 4893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6660 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4039, some c4067, some c4015, some c5372, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p6660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6660 : lratChecker f6660 p6660 = .success := by decide +kernel
theorem unsat6660 : Unsatisfiable (PosFin 65) f6660 := by
  apply lratCheckerSound f6660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6660
  · intro a ha; simp [p6660] at ha; subst a; trivial
  · exact checked6660
theorem derived6660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6660 := by
  apply localUnsat_implies_entails f6660 [c4039, c4067, c4015, c5372] c6660 unsat6660 (by rfl) a
  have h0 : Entails.eval a c4039 := h 4038 (by decide)
  have h1 : Entails.eval a c4067 := h 4066 (by decide)
  have h2 : Entails.eval a c4015 := h 4014 (by decide)
  have h3 : Entails.eval a c5372 := h 5371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6661 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6661 : lratChecker f6661 p6661 = .success := by decide +kernel
theorem unsat6661 : Unsatisfiable (PosFin 65) f6661 := by
  apply lratCheckerSound f6661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6661
  · intro a ha; simp [p6661] at ha; subst a; trivial
  · exact checked6661
theorem derived6661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6661 := by
  apply localUnsat_implies_entails f6661 [c6581, c4] c6661 unsat6661 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6662 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c8, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6662 : lratChecker f6662 p6662 = .success := by decide +kernel
theorem unsat6662 : Unsatisfiable (PosFin 65) f6662 := by
  apply lratCheckerSound f6662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6662
  · intro a ha; simp [p6662] at ha; subst a; trivial
  · exact checked6662
theorem derived6662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6662 := by
  apply localUnsat_implies_entails f6662 [c6581, c8] c6662 unsat6662 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6663 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c9, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6663 : lratChecker f6663 p6663 = .success := by decide +kernel
theorem unsat6663 : Unsatisfiable (PosFin 65) f6663 := by
  apply lratCheckerSound f6663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6663
  · intro a ha; simp [p6663] at ha; subst a; trivial
  · exact checked6663
theorem derived6663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6663 := by
  apply localUnsat_implies_entails f6663 [c6581, c9] c6663 unsat6663 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6664 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c10, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6664 : lratChecker f6664 p6664 = .success := by decide +kernel
theorem unsat6664 : Unsatisfiable (PosFin 65) f6664 := by
  apply lratCheckerSound f6664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6664
  · intro a ha; simp [p6664] at ha; subst a; trivial
  · exact checked6664
theorem derived6664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6664 := by
  apply localUnsat_implies_entails f6664 [c6581, c10] c6664 unsat6664 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6665 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c11, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6665 : lratChecker f6665 p6665 = .success := by decide +kernel
theorem unsat6665 : Unsatisfiable (PosFin 65) f6665 := by
  apply lratCheckerSound f6665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6665
  · intro a ha; simp [p6665] at ha; subst a; trivial
  · exact checked6665
theorem derived6665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6665 := by
  apply localUnsat_implies_entails f6665 [c6581, c11] c6665 unsat6665 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6666 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c19, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6666 : lratChecker f6666 p6666 = .success := by decide +kernel
theorem unsat6666 : Unsatisfiable (PosFin 65) f6666 := by
  apply lratCheckerSound f6666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6666
  · intro a ha; simp [p6666] at ha; subst a; trivial
  · exact checked6666
theorem derived6666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6666 := by
  apply localUnsat_implies_entails f6666 [c6581, c19] c6666 unsat6666 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6667 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c21, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6667 : lratChecker f6667 p6667 = .success := by decide +kernel
theorem unsat6667 : Unsatisfiable (PosFin 65) f6667 := by
  apply lratCheckerSound f6667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6667
  · intro a ha; simp [p6667] at ha; subst a; trivial
  · exact checked6667
theorem derived6667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6667 := by
  apply localUnsat_implies_entails f6667 [c6581, c21] c6667 unsat6667 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6668 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c23, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6668 : lratChecker f6668 p6668 = .success := by decide +kernel
theorem unsat6668 : Unsatisfiable (PosFin 65) f6668 := by
  apply lratCheckerSound f6668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6668
  · intro a ha; simp [p6668] at ha; subst a; trivial
  · exact checked6668
theorem derived6668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6668 := by
  apply localUnsat_implies_entails f6668 [c6581, c23] c6668 unsat6668 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6669 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c25, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6669 : lratChecker f6669 p6669 = .success := by decide +kernel
theorem unsat6669 : Unsatisfiable (PosFin 65) f6669 := by
  apply lratCheckerSound f6669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6669
  · intro a ha; simp [p6669] at ha; subst a; trivial
  · exact checked6669
theorem derived6669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6669 := by
  apply localUnsat_implies_entails f6669 [c6581, c25] c6669 unsat6669 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6670 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c26, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6670 : lratChecker f6670 p6670 = .success := by decide +kernel
theorem unsat6670 : Unsatisfiable (PosFin 65) f6670 := by
  apply lratCheckerSound f6670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6670
  · intro a ha; simp [p6670] at ha; subst a; trivial
  · exact checked6670
theorem derived6670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6670 := by
  apply localUnsat_implies_entails f6670 [c6581, c26] c6670 unsat6670 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6671 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c30, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6671 : lratChecker f6671 p6671 = .success := by decide +kernel
theorem unsat6671 : Unsatisfiable (PosFin 65) f6671 := by
  apply lratCheckerSound f6671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6671
  · intro a ha; simp [p6671] at ha; subst a; trivial
  · exact checked6671
theorem derived6671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6671 := by
  apply localUnsat_implies_entails f6671 [c6581, c30] c6671 unsat6671 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6672 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c31, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6672 : lratChecker f6672 p6672 = .success := by decide +kernel
theorem unsat6672 : Unsatisfiable (PosFin 65) f6672 := by
  apply lratCheckerSound f6672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6672
  · intro a ha; simp [p6672] at ha; subst a; trivial
  · exact checked6672
theorem derived6672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6672 := by
  apply localUnsat_implies_entails f6672 [c6581, c31] c6672 unsat6672 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6673 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c33, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6673 : lratChecker f6673 p6673 = .success := by decide +kernel
theorem unsat6673 : Unsatisfiable (PosFin 65) f6673 := by
  apply lratCheckerSound f6673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6673
  · intro a ha; simp [p6673] at ha; subst a; trivial
  · exact checked6673
theorem derived6673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6673 := by
  apply localUnsat_implies_entails f6673 [c6581, c33] c6673 unsat6673 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6674 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, false), (⟨3, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c35, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6674 : lratChecker f6674 p6674 = .success := by decide +kernel
theorem unsat6674 : Unsatisfiable (PosFin 65) f6674 := by
  apply lratCheckerSound f6674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6674
  · intro a ha; simp [p6674] at ha; subst a; trivial
  · exact checked6674
theorem derived6674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6674 := by
  apply localUnsat_implies_entails f6674 [c6581, c35] c6674 unsat6674 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6675 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c44, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6675 : lratChecker f6675 p6675 = .success := by decide +kernel
theorem unsat6675 : Unsatisfiable (PosFin 65) f6675 := by
  apply lratCheckerSound f6675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6675
  · intro a ha; simp [p6675] at ha; subst a; trivial
  · exact checked6675
theorem derived6675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6675 := by
  apply localUnsat_implies_entails f6675 [c6581, c44] c6675 unsat6675 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6676 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c47, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6676 : lratChecker f6676 p6676 = .success := by decide +kernel
theorem unsat6676 : Unsatisfiable (PosFin 65) f6676 := by
  apply lratCheckerSound f6676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6676
  · intro a ha; simp [p6676] at ha; subst a; trivial
  · exact checked6676
theorem derived6676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6676 := by
  apply localUnsat_implies_entails f6676 [c6581, c47] c6676 unsat6676 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6677 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c52, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6677 : lratChecker f6677 p6677 = .success := by decide +kernel
theorem unsat6677 : Unsatisfiable (PosFin 65) f6677 := by
  apply lratCheckerSound f6677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6677
  · intro a ha; simp [p6677] at ha; subst a; trivial
  · exact checked6677
theorem derived6677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6677 := by
  apply localUnsat_implies_entails f6677 [c6581, c52] c6677 unsat6677 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6678 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c53, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6678 : lratChecker f6678 p6678 = .success := by decide +kernel
theorem unsat6678 : Unsatisfiable (PosFin 65) f6678 := by
  apply lratCheckerSound f6678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6678
  · intro a ha; simp [p6678] at ha; subst a; trivial
  · exact checked6678
theorem derived6678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6678 := by
  apply localUnsat_implies_entails f6678 [c6581, c53] c6678 unsat6678 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6679 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c54, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6679 : lratChecker f6679 p6679 = .success := by decide +kernel
theorem unsat6679 : Unsatisfiable (PosFin 65) f6679 := by
  apply lratCheckerSound f6679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6679
  · intro a ha; simp [p6679] at ha; subst a; trivial
  · exact checked6679
theorem derived6679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6679 := by
  apply localUnsat_implies_entails f6679 [c6581, c54] c6679 unsat6679 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6680 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c57, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6680 : lratChecker f6680 p6680 = .success := by decide +kernel
theorem unsat6680 : Unsatisfiable (PosFin 65) f6680 := by
  apply lratCheckerSound f6680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6680
  · intro a ha; simp [p6680] at ha; subst a; trivial
  · exact checked6680
theorem derived6680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6680 := by
  apply localUnsat_implies_entails f6680 [c6581, c57] c6680 unsat6680 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived6680

end CochromaticTwenty.Certificates.FixedCore1
