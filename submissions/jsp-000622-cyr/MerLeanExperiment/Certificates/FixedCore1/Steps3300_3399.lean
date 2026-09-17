import MerLeanExperiment.Certificates.FixedCore1.Steps3200_3299

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9181 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨43, by decide⟩, true), (⟨40, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4715, some c5304, some c4677, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9181 : lratChecker f9181 p9181 = .success := by decide +kernel
theorem unsat9181 : Unsatisfiable (PosFin 65) f9181 := by
  apply lratCheckerSound f9181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9181
  · intro a ha; simp [p9181] at ha; subst a; trivial
  · exact checked9181
theorem derived9181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9181 := by
  apply localUnsat_implies_entails f9181 [c4715, c5304, c4677] c9181 unsat9181 (by rfl) a
  have h0 : Entails.eval a c4715 := h 4714 (by decide)
  have h1 : Entails.eval a c5304 := h 5303 (by decide)
  have h2 : Entails.eval a c4677 := h 4676 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9182 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c9179, some c9178, some c9177, some c3891, some c9180, some c9068, some c9181, some c4377, some c6781, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9182 : lratChecker f9182 p9182 = .success := by decide +kernel
theorem unsat9182 : Unsatisfiable (PosFin 65) f9182 := by
  apply lratCheckerSound f9182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9182
  · intro a ha; simp [p9182] at ha; subst a; trivial
  · exact checked9182
theorem derived9182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9182 := by
  apply localUnsat_implies_entails f9182 [c9173, c7129, c9179, c9178, c9177, c3891, c9180, c9068, c9181, c4377, c6781] c9182 unsat9182 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9179 := derived9179 a h
  have h3 : Entails.eval a c9178 := derived9178 a h
  have h4 : Entails.eval a c9177 := derived9177 a h
  have h5 : Entails.eval a c3891 := h 3890 (by decide)
  have h6 : Entails.eval a c9180 := derived9180 a h
  have h7 : Entails.eval a c9068 := derived9068 a h
  have h8 : Entails.eval a c9181 := derived9181 a h
  have h9 : Entails.eval a c4377 := h 4376 (by decide)
  have h10 : Entails.eval a c6781 := derived6781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9183 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9173, some c9179, some c9182, some c3740, some c5607, some c3834, some c3456, some c4253, some c4261, some c4254, some c3811, some c5653, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9183 : lratChecker f9183 p9183 = .success := by decide +kernel
theorem unsat9183 : Unsatisfiable (PosFin 65) f9183 := by
  apply lratCheckerSound f9183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9183
  · intro a ha; simp [p9183] at ha; subst a; trivial
  · exact checked9183
theorem derived9183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9183 := by
  apply localUnsat_implies_entails f9183 [c7129, c9173, c9179, c9182, c3740, c5607, c3834, c3456, c4253, c4261, c4254, c3811, c5653] c9183 unsat9183 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c9179 := derived9179 a h
  have h3 : Entails.eval a c9182 := derived9182 a h
  have h4 : Entails.eval a c3740 := h 3739 (by decide)
  have h5 : Entails.eval a c5607 := h 5606 (by decide)
  have h6 : Entails.eval a c3834 := h 3833 (by decide)
  have h7 : Entails.eval a c3456 := h 3455 (by decide)
  have h8 : Entails.eval a c4253 := h 4252 (by decide)
  have h9 : Entails.eval a c4261 := h 4260 (by decide)
  have h10 : Entails.eval a c4254 := h 4253 (by decide)
  have h11 : Entails.eval a c3811 := h 3810 (by decide)
  have h12 : Entails.eval a c5653 := h 5652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9184 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c9179, some c9182, some c5607, some c3740, some c9183, some c9176, some c3805, some c5653, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9184 : lratChecker f9184 p9184 = .success := by decide +kernel
theorem unsat9184 : Unsatisfiable (PosFin 65) f9184 := by
  apply lratCheckerSound f9184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9184
  · intro a ha; simp [p9184] at ha; subst a; trivial
  · exact checked9184
theorem derived9184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9184 := by
  apply localUnsat_implies_entails f9184 [c9173, c7129, c9179, c9182, c5607, c3740, c9183, c9176, c3805, c5653] c9184 unsat9184 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9179 := derived9179 a h
  have h3 : Entails.eval a c9182 := derived9182 a h
  have h4 : Entails.eval a c5607 := h 5606 (by decide)
  have h5 : Entails.eval a c3740 := h 3739 (by decide)
  have h6 : Entails.eval a c9183 := derived9183 a h
  have h7 : Entails.eval a c9176 := derived9176 a h
  have h8 : Entails.eval a c3805 := h 3804 (by decide)
  have h9 : Entails.eval a c5653 := h 5652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9185 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c4792, some c5604, some c4940, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9185 : lratChecker f9185 p9185 = .success := by decide +kernel
theorem unsat9185 : Unsatisfiable (PosFin 65) f9185 := by
  apply lratCheckerSound f9185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9185
  · intro a ha; simp [p9185] at ha; subst a; trivial
  · exact checked9185
theorem derived9185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9185 := by
  apply localUnsat_implies_entails f9185 [c9173, c4792, c5604, c4940] c9185 unsat9185 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c4792 := h 4791 (by decide)
  have h2 : Entails.eval a c5604 := h 5603 (by decide)
  have h3 : Entails.eval a c4940 := h 4939 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9186 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9184, some c9173, some c7129, some c5582, some c5843, some c4940, some c6930, some c4770, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9186 : lratChecker f9186 p9186 = .success := by decide +kernel
theorem unsat9186 : Unsatisfiable (PosFin 65) f9186 := by
  apply lratCheckerSound f9186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9186
  · intro a ha; simp [p9186] at ha; subst a; trivial
  · exact checked9186
theorem derived9186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9186 := by
  apply localUnsat_implies_entails f9186 [c9184, c9173, c7129, c5582, c5843, c4940, c6930, c4770] c9186 unsat9186 (by rfl) a
  have h0 : Entails.eval a c9184 := derived9184 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c5582 := h 5581 (by decide)
  have h4 : Entails.eval a c5843 := h 5842 (by decide)
  have h5 : Entails.eval a c4940 := h 4939 (by decide)
  have h6 : Entails.eval a c6930 := derived6930 a h
  have h7 : Entails.eval a c4770 := h 4769 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9187 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5535, some c4859, some c5264, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9187 : lratChecker f9187 p9187 = .success := by decide +kernel
theorem unsat9187 : Unsatisfiable (PosFin 65) f9187 := by
  apply lratCheckerSound f9187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9187
  · intro a ha; simp [p9187] at ha; subst a; trivial
  · exact checked9187
theorem derived9187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9187 := by
  apply localUnsat_implies_entails f9187 [c5535, c4859, c5264] c9187 unsat9187 (by rfl) a
  have h0 : Entails.eval a c5535 := h 5534 (by decide)
  have h1 : Entails.eval a c4859 := h 4858 (by decide)
  have h2 : Entails.eval a c5264 := h 5263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9188 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9184, some c9140, some c9185, some c9186, some c9173, some c7129, some c4695, some c5320, some c9187, some c9180, some c4540, some c4549, some c4544, some c5183, some c3870, some c5209, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9188 : lratChecker f9188 p9188 = .success := by decide +kernel
theorem unsat9188 : Unsatisfiable (PosFin 65) f9188 := by
  apply lratCheckerSound f9188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9188
  · intro a ha; simp [p9188] at ha; subst a; trivial
  · exact checked9188
theorem derived9188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9188 := by
  apply localUnsat_implies_entails f9188 [c9184, c9140, c9185, c9186, c9173, c7129, c4695, c5320, c9187, c9180, c4540, c4549, c4544, c5183, c3870, c5209] c9188 unsat9188 (by rfl) a
  have h0 : Entails.eval a c9184 := derived9184 a h
  have h1 : Entails.eval a c9140 := derived9140 a h
  have h2 : Entails.eval a c9185 := derived9185 a h
  have h3 : Entails.eval a c9186 := derived9186 a h
  have h4 : Entails.eval a c9173 := derived9173 a h
  have h5 : Entails.eval a c7129 := derived7129 a h
  have h6 : Entails.eval a c4695 := h 4694 (by decide)
  have h7 : Entails.eval a c5320 := h 5319 (by decide)
  have h8 : Entails.eval a c9187 := derived9187 a h
  have h9 : Entails.eval a c9180 := derived9180 a h
  have h10 : Entails.eval a c4540 := h 4539 (by decide)
  have h11 : Entails.eval a c4549 := h 4548 (by decide)
  have h12 : Entails.eval a c4544 := h 4543 (by decide)
  have h13 : Entails.eval a c5183 := h 5182 (by decide)
  have h14 : Entails.eval a c3870 := h 3869 (by decide)
  have h15 : Entails.eval a c5209 := h 5208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9189 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9186, some c9184, some c9173, some c7129, some c9188, some c4901, some c9177, some c4377, some c6781, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9189 : lratChecker f9189 p9189 = .success := by decide +kernel
theorem unsat9189 : Unsatisfiable (PosFin 65) f9189 := by
  apply lratCheckerSound f9189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9189
  · intro a ha; simp [p9189] at ha; subst a; trivial
  · exact checked9189
theorem derived9189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9189 := by
  apply localUnsat_implies_entails f9189 [c9186, c9184, c9173, c7129, c9188, c4901, c9177, c4377, c6781] c9189 unsat9189 (by rfl) a
  have h0 : Entails.eval a c9186 := derived9186 a h
  have h1 : Entails.eval a c9184 := derived9184 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9188 := derived9188 a h
  have h5 : Entails.eval a c4901 := h 4900 (by decide)
  have h6 : Entails.eval a c9177 := derived9177 a h
  have h7 : Entails.eval a c4377 := h 4376 (by decide)
  have h8 : Entails.eval a c6781 := derived6781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9190 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9184, some c9173, some c9186, some c9189, some c3889, some c4901, some c3736, some c5712, some c3716, some c5487, some c4859, some c7129, some c4619, some c6888, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9190 : lratChecker f9190 p9190 = .success := by decide +kernel
theorem unsat9190 : Unsatisfiable (PosFin 65) f9190 := by
  apply lratCheckerSound f9190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9190
  · intro a ha; simp [p9190] at ha; subst a; trivial
  · exact checked9190
theorem derived9190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9190 := by
  apply localUnsat_implies_entails f9190 [c9184, c9173, c9186, c9189, c3889, c4901, c3736, c5712, c3716, c5487, c4859, c7129, c4619, c6888] c9190 unsat9190 (by rfl) a
  have h0 : Entails.eval a c9184 := derived9184 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c9186 := derived9186 a h
  have h3 : Entails.eval a c9189 := derived9189 a h
  have h4 : Entails.eval a c3889 := h 3888 (by decide)
  have h5 : Entails.eval a c4901 := h 4900 (by decide)
  have h6 : Entails.eval a c3736 := h 3735 (by decide)
  have h7 : Entails.eval a c5712 := h 5711 (by decide)
  have h8 : Entails.eval a c3716 := h 3715 (by decide)
  have h9 : Entails.eval a c5487 := h 5486 (by decide)
  have h10 : Entails.eval a c4859 := h 4858 (by decide)
  have h11 : Entails.eval a c7129 := derived7129 a h
  have h12 : Entails.eval a c4619 := h 4618 (by decide)
  have h13 : Entails.eval a c6888 := derived6888 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9191 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨43, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨47, by decide⟩, true), (⟨51, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3611, some c6965, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9191 : lratChecker f9191 p9191 = .success := by decide +kernel
theorem unsat9191 : Unsatisfiable (PosFin 65) f9191 := by
  apply lratCheckerSound f9191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9191
  · intro a ha; simp [p9191] at ha; subst a; trivial
  · exact checked9191
theorem derived9191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9191 := by
  apply localUnsat_implies_entails f9191 [c3611, c6965] c9191 unsat9191 (by rfl) a
  have h0 : Entails.eval a c3611 := h 3610 (by decide)
  have h1 : Entails.eval a c6965 := derived6965 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9192 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c9184, some c9186, some c9189, some c3736, some c3889, some c4901, some c5712, some c3716, some c5487, some c4859, some c9190, some c9191, some c5900, some c4412, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9192 : lratChecker f9192 p9192 = .success := by decide +kernel
theorem unsat9192 : Unsatisfiable (PosFin 65) f9192 := by
  apply lratCheckerSound f9192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9192
  · intro a ha; simp [p9192] at ha; subst a; trivial
  · exact checked9192
theorem derived9192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9192 := by
  apply localUnsat_implies_entails f9192 [c9173, c7129, c9184, c9186, c9189, c3736, c3889, c4901, c5712, c3716, c5487, c4859, c9190, c9191, c5900, c4412] c9192 unsat9192 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9184 := derived9184 a h
  have h3 : Entails.eval a c9186 := derived9186 a h
  have h4 : Entails.eval a c9189 := derived9189 a h
  have h5 : Entails.eval a c3736 := h 3735 (by decide)
  have h6 : Entails.eval a c3889 := h 3888 (by decide)
  have h7 : Entails.eval a c4901 := h 4900 (by decide)
  have h8 : Entails.eval a c5712 := h 5711 (by decide)
  have h9 : Entails.eval a c3716 := h 3715 (by decide)
  have h10 : Entails.eval a c5487 := h 5486 (by decide)
  have h11 : Entails.eval a c4859 := h 4858 (by decide)
  have h12 : Entails.eval a c9190 := derived9190 a h
  have h13 : Entails.eval a c9191 := derived9191 a h
  have h14 : Entails.eval a c5900 := derived5900 a h
  have h15 : Entails.eval a c4412 := h 4411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9193 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨60, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4613, some c5852, some c4546, some c6878, some c6974, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p9193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9193 : lratChecker f9193 p9193 = .success := by decide +kernel
theorem unsat9193 : Unsatisfiable (PosFin 65) f9193 := by
  apply lratCheckerSound f9193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9193
  · intro a ha; simp [p9193] at ha; subst a; trivial
  · exact checked9193
theorem derived9193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9193 := by
  apply localUnsat_implies_entails f9193 [c4613, c5852, c4546, c6878, c6974] c9193 unsat9193 (by rfl) a
  have h0 : Entails.eval a c4613 := h 4612 (by decide)
  have h1 : Entails.eval a c5852 := h 5851 (by decide)
  have h2 : Entails.eval a c4546 := h 4545 (by decide)
  have h3 : Entails.eval a c6878 := derived6878 a h
  have h4 : Entails.eval a c6974 := derived6974 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9194 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨47, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9192, some c4546, some c6907, some c6980, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9194 : lratChecker f9194 p9194 = .success := by decide +kernel
theorem unsat9194 : Unsatisfiable (PosFin 65) f9194 := by
  apply lratCheckerSound f9194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9194
  · intro a ha; simp [p9194] at ha; subst a; trivial
  · exact checked9194
theorem derived9194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9194 := by
  apply localUnsat_implies_entails f9194 [c9192, c4546, c6907, c6980] c9194 unsat9194 (by rfl) a
  have h0 : Entails.eval a c9192 := derived9192 a h
  have h1 : Entails.eval a c4546 := h 4545 (by decide)
  have h2 : Entails.eval a c6907 := derived6907 a h
  have h3 : Entails.eval a c6980 := derived6980 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9195 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9192, some c9173, some c9193, some c4369, some c4587, some c4867, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9195 : lratChecker f9195 p9195 = .success := by decide +kernel
theorem unsat9195 : Unsatisfiable (PosFin 65) f9195 := by
  apply lratCheckerSound f9195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9195
  · intro a ha; simp [p9195] at ha; subst a; trivial
  · exact checked9195
theorem derived9195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9195 := by
  apply localUnsat_implies_entails f9195 [c9192, c9173, c9193, c4369, c4587, c4867] c9195 unsat9195 (by rfl) a
  have h0 : Entails.eval a c9192 := derived9192 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c4369 := h 4368 (by decide)
  have h4 : Entails.eval a c4587 := h 4586 (by decide)
  have h5 : Entails.eval a c4867 := h 4866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9196 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9195, some c9192, some c6878, some c9194, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9196 : lratChecker f9196 p9196 = .success := by decide +kernel
theorem unsat9196 : Unsatisfiable (PosFin 65) f9196 := by
  apply lratCheckerSound f9196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9196
  · intro a ha; simp [p9196] at ha; subst a; trivial
  · exact checked9196
theorem derived9196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9196 := by
  apply localUnsat_implies_entails f9196 [c9195, c9192, c6878, c9194] c9196 unsat9196 (by rfl) a
  have h0 : Entails.eval a c9195 := derived9195 a h
  have h1 : Entails.eval a c9192 := derived9192 a h
  have h2 : Entails.eval a c6878 := derived6878 a h
  have h3 : Entails.eval a c9194 := derived9194 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9197 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9196, some c4948, some c5591, some c6931, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9197 : lratChecker f9197 p9197 = .success := by decide +kernel
theorem unsat9197 : Unsatisfiable (PosFin 65) f9197 := by
  apply lratCheckerSound f9197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9197
  · intro a ha; simp [p9197] at ha; subst a; trivial
  · exact checked9197
theorem derived9197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9197 := by
  apply localUnsat_implies_entails f9197 [c9193, c9196, c4948, c5591, c6931] c9197 unsat9197 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9196 := derived9196 a h
  have h2 : Entails.eval a c4948 := h 4947 (by decide)
  have h3 : Entails.eval a c5591 := h 5590 (by decide)
  have h4 : Entails.eval a c6931 := derived6931 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9198 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c9192, some c9197, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9198 : lratChecker f9198 p9198 = .success := by decide +kernel
theorem unsat9198 : Unsatisfiable (PosFin 65) f9198 := by
  apply lratCheckerSound f9198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9198
  · intro a ha; simp [p9198] at ha; subst a; trivial
  · exact checked9198
theorem derived9198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9198 := by
  apply localUnsat_implies_entails f9198 [c9173, c9192, c9197] c9198 unsat9198 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c9192 := derived9192 a h
  have h2 : Entails.eval a c9197 := derived9197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9199 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c7129, some c4750, some c4754, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9199 : lratChecker f9199 p9199 = .success := by decide +kernel
theorem unsat9199 : Unsatisfiable (PosFin 65) f9199 := by
  apply lratCheckerSound f9199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9199
  · intro a ha; simp [p9199] at ha; subst a; trivial
  · exact checked9199
theorem derived9199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9199 := by
  apply localUnsat_implies_entails f9199 [c9198, c7129, c4750, c4754] c9199 unsat9199 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c4750 := h 4749 (by decide)
  have h3 : Entails.eval a c4754 := h 4753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9200 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c7129, some c5572, some c5574, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9200 : lratChecker f9200 p9200 = .success := by decide +kernel
theorem unsat9200 : Unsatisfiable (PosFin 65) f9200 := by
  apply lratCheckerSound f9200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9200
  · intro a ha; simp [p9200] at ha; subst a; trivial
  · exact checked9200
theorem derived9200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9200 := by
  apply localUnsat_implies_entails f9200 [c9198, c9173, c7129, c5572, c5574] c9200 unsat9200 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c5572 := h 5571 (by decide)
  have h4 : Entails.eval a c5574 := h 5573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9201 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c7129, some c4931, some c4935, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9201 : lratChecker f9201 p9201 = .success := by decide +kernel
theorem unsat9201 : Unsatisfiable (PosFin 65) f9201 := by
  apply lratCheckerSound f9201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9201
  · intro a ha; simp [p9201] at ha; subst a; trivial
  · exact checked9201
theorem derived9201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9201 := by
  apply localUnsat_implies_entails f9201 [c9198, c9173, c7129, c4931, c4935] c9201 unsat9201 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c4931 := h 4930 (by decide)
  have h4 : Entails.eval a c4935 := h 4934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9202 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c9200, some c9201, some c9199, some c5835, some c5840, some c5832, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9202 : lratChecker f9202 p9202 = .success := by decide +kernel
theorem unsat9202 : Unsatisfiable (PosFin 65) f9202 := by
  apply lratCheckerSound f9202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9202
  · intro a ha; simp [p9202] at ha; subst a; trivial
  · exact checked9202
theorem derived9202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9202 := by
  apply localUnsat_implies_entails f9202 [c9198, c9173, c9200, c9201, c9199, c5835, c5840, c5832] c9202 unsat9202 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c9200 := derived9200 a h
  have h3 : Entails.eval a c9201 := derived9201 a h
  have h4 : Entails.eval a c9199 := derived9199 a h
  have h5 : Entails.eval a c5835 := h 5834 (by decide)
  have h6 : Entails.eval a c5840 := h 5839 (by decide)
  have h7 : Entails.eval a c5832 := h 5831 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9203 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c7129, some c4600, some c5178, some c4402, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9203 : lratChecker f9203 p9203 = .success := by decide +kernel
theorem unsat9203 : Unsatisfiable (PosFin 65) f9203 := by
  apply lratCheckerSound f9203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9203
  · intro a ha; simp [p9203] at ha; subst a; trivial
  · exact checked9203
theorem derived9203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9203 := by
  apply localUnsat_implies_entails f9203 [c9198, c9173, c7129, c4600, c5178, c4402] c9203 unsat9203 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c4600 := h 4599 (by decide)
  have h4 : Entails.eval a c5178 := h 5177 (by decide)
  have h5 : Entails.eval a c4402 := h 4401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9204 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨35, by decide⟩, true), (⟨53, by decide⟩, true), (⟨62, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4532, some c6904, some c6875, some c6976, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9204 : lratChecker f9204 p9204 = .success := by decide +kernel
theorem unsat9204 : Unsatisfiable (PosFin 65) f9204 := by
  apply lratCheckerSound f9204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9204
  · intro a ha; simp [p9204] at ha; subst a; trivial
  · exact checked9204
theorem derived9204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9204 := by
  apply localUnsat_implies_entails f9204 [c4532, c6904, c6875, c6976] c9204 unsat9204 (by rfl) a
  have h0 : Entails.eval a c4532 := h 4531 (by decide)
  have h1 : Entails.eval a c6904 := derived6904 a h
  have h2 : Entails.eval a c6875 := derived6875 a h
  have h3 : Entails.eval a c6976 := derived6976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9205 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9202, some c9173, some c9203, some c4596, some c9204, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9205 : lratChecker f9205 p9205 = .success := by decide +kernel
theorem unsat9205 : Unsatisfiable (PosFin 65) f9205 := by
  apply lratCheckerSound f9205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9205
  · intro a ha; simp [p9205] at ha; subst a; trivial
  · exact checked9205
theorem derived9205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9205 := by
  apply localUnsat_implies_entails f9205 [c9202, c9173, c9203, c4596, c9204] c9205 unsat9205 (by rfl) a
  have h0 : Entails.eval a c9202 := derived9202 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c9203 := derived9203 a h
  have h3 : Entails.eval a c4596 := h 4595 (by decide)
  have h4 : Entails.eval a c9204 := derived9204 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9206 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9205, some c9202, some c9173, some c9204, some c4355, some c4574, some c6940, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9206 : lratChecker f9206 p9206 = .success := by decide +kernel
theorem unsat9206 : Unsatisfiable (PosFin 65) f9206 := by
  apply lratCheckerSound f9206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9206
  · intro a ha; simp [p9206] at ha; subst a; trivial
  · exact checked9206
theorem derived9206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9206 := by
  apply localUnsat_implies_entails f9206 [c9205, c9202, c9173, c9204, c4355, c4574, c6940] c9206 unsat9206 (by rfl) a
  have h0 : Entails.eval a c9205 := derived9205 a h
  have h1 : Entails.eval a c9202 := derived9202 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c9204 := derived9204 a h
  have h4 : Entails.eval a c4355 := h 4354 (by decide)
  have h5 : Entails.eval a c4574 := h 4573 (by decide)
  have h6 : Entails.eval a c6940 := derived6940 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9207 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9206, some c9205, some c9202, some c9198, some c9173, some c7129, some c4360, some c9199, some c4710, some c5025, some c9096, some c4579, some c6942, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9207 : lratChecker f9207 p9207 = .success := by decide +kernel
theorem unsat9207 : Unsatisfiable (PosFin 65) f9207 := by
  apply lratCheckerSound f9207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9207
  · intro a ha; simp [p9207] at ha; subst a; trivial
  · exact checked9207
theorem derived9207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9207 := by
  apply localUnsat_implies_entails f9207 [c9206, c9205, c9202, c9198, c9173, c7129, c4360, c9199, c4710, c5025, c9096, c4579, c6942] c9207 unsat9207 (by rfl) a
  have h0 : Entails.eval a c9206 := derived9206 a h
  have h1 : Entails.eval a c9205 := derived9205 a h
  have h2 : Entails.eval a c9202 := derived9202 a h
  have h3 : Entails.eval a c9198 := derived9198 a h
  have h4 : Entails.eval a c9173 := derived9173 a h
  have h5 : Entails.eval a c7129 := derived7129 a h
  have h6 : Entails.eval a c4360 := h 4359 (by decide)
  have h7 : Entails.eval a c9199 := derived9199 a h
  have h8 : Entails.eval a c4710 := h 4709 (by decide)
  have h9 : Entails.eval a c5025 := h 5024 (by decide)
  have h10 : Entails.eval a c9096 := derived9096 a h
  have h11 : Entails.eval a c4579 := h 4578 (by decide)
  have h12 : Entails.eval a c6942 := derived6942 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9208 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c7129, some c9202, some c9206, some c9207, some c4402, some c4624, some c5231, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9208 : lratChecker f9208 p9208 = .success := by decide +kernel
theorem unsat9208 : Unsatisfiable (PosFin 65) f9208 := by
  apply lratCheckerSound f9208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9208
  · intro a ha; simp [p9208] at ha; subst a; trivial
  · exact checked9208
theorem derived9208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9208 := by
  apply localUnsat_implies_entails f9208 [c9198, c9173, c7129, c9202, c9206, c9207, c4402, c4624, c5231] c9208 unsat9208 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9202 := derived9202 a h
  have h4 : Entails.eval a c9206 := derived9206 a h
  have h5 : Entails.eval a c9207 := derived9207 a h
  have h6 : Entails.eval a c4402 := h 4401 (by decide)
  have h7 : Entails.eval a c4624 := h 4623 (by decide)
  have h8 : Entails.eval a c5231 := h 5230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9209 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨49, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c7129, some c4402, some c4624, some c5231, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9209 : lratChecker f9209 p9209 = .success := by decide +kernel
theorem unsat9209 : Unsatisfiable (PosFin 65) f9209 := by
  apply lratCheckerSound f9209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9209
  · intro a ha; simp [p9209] at ha; subst a; trivial
  · exact checked9209
theorem derived9209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9209 := by
  apply localUnsat_implies_entails f9209 [c9198, c9173, c7129, c4402, c4624, c5231] c9209 unsat9209 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c4402 := h 4401 (by decide)
  have h4 : Entails.eval a c4624 := h 4623 (by decide)
  have h5 : Entails.eval a c5231 := h 5230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9210 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨49, by decide⟩, false), (⟨58, by decide⟩, false), (⟨48, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5838, some c4935, some c5574, some c4754, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p9210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9210 : lratChecker f9210 p9210 = .success := by decide +kernel
theorem unsat9210 : Unsatisfiable (PosFin 65) f9210 := by
  apply lratCheckerSound f9210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9210
  · intro a ha; simp [p9210] at ha; subst a; trivial
  · exact checked9210
theorem derived9210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9210 := by
  apply localUnsat_implies_entails f9210 [c5838, c4935, c5574, c4754] c9210 unsat9210 (by rfl) a
  have h0 : Entails.eval a c5838 := h 5837 (by decide)
  have h1 : Entails.eval a c4935 := h 4934 (by decide)
  have h2 : Entails.eval a c5574 := h 5573 (by decide)
  have h3 : Entails.eval a c4754 := h 4753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9211 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨49, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9198, some c9173, some c7129, some c9210, some c9203, some c9209, some c4360, some c4754, some c5025, some c4710, some c9096, some c9208, some c4853, some c6941, some c4649, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9211 : lratChecker f9211 p9211 = .success := by decide +kernel
theorem unsat9211 : Unsatisfiable (PosFin 65) f9211 := by
  apply lratCheckerSound f9211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9211
  · intro a ha; simp [p9211] at ha; subst a; trivial
  · exact checked9211
theorem derived9211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9211 := by
  apply localUnsat_implies_entails f9211 [c9198, c9173, c7129, c9210, c9203, c9209, c4360, c4754, c5025, c4710, c9096, c9208, c4853, c6941, c4649] c9211 unsat9211 (by rfl) a
  have h0 : Entails.eval a c9198 := derived9198 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9210 := derived9210 a h
  have h4 : Entails.eval a c9203 := derived9203 a h
  have h5 : Entails.eval a c9209 := derived9209 a h
  have h6 : Entails.eval a c4360 := h 4359 (by decide)
  have h7 : Entails.eval a c4754 := h 4753 (by decide)
  have h8 : Entails.eval a c5025 := h 5024 (by decide)
  have h9 : Entails.eval a c4710 := h 4709 (by decide)
  have h10 : Entails.eval a c9096 := derived9096 a h
  have h11 : Entails.eval a c9208 := derived9208 a h
  have h12 : Entails.eval a c4853 := h 4852 (by decide)
  have h13 : Entails.eval a c6941 := derived6941 a h
  have h14 : Entails.eval a c4649 := h 4648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9212 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9208, some c9198, some c9173, some c7129, some c9210, some c9203, some c9209, some c4360, some c4754, some c4710, some c5025, some c9096, some c9211, some c5482, some c5266, some c6991, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9212 : lratChecker f9212 p9212 = .success := by decide +kernel
theorem unsat9212 : Unsatisfiable (PosFin 65) f9212 := by
  apply lratCheckerSound f9212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9212
  · intro a ha; simp [p9212] at ha; subst a; trivial
  · exact checked9212
theorem derived9212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9212 := by
  apply localUnsat_implies_entails f9212 [c9208, c9198, c9173, c7129, c9210, c9203, c9209, c4360, c4754, c4710, c5025, c9096, c9211, c5482, c5266, c6991] c9212 unsat9212 (by rfl) a
  have h0 : Entails.eval a c9208 := derived9208 a h
  have h1 : Entails.eval a c9198 := derived9198 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9210 := derived9210 a h
  have h5 : Entails.eval a c9203 := derived9203 a h
  have h6 : Entails.eval a c9209 := derived9209 a h
  have h7 : Entails.eval a c4360 := h 4359 (by decide)
  have h8 : Entails.eval a c4754 := h 4753 (by decide)
  have h9 : Entails.eval a c4710 := h 4709 (by decide)
  have h10 : Entails.eval a c5025 := h 5024 (by decide)
  have h11 : Entails.eval a c9096 := derived9096 a h
  have h12 : Entails.eval a c9211 := derived9211 a h
  have h13 : Entails.eval a c5482 := h 5481 (by decide)
  have h14 : Entails.eval a c5266 := h 5265 (by decide)
  have h15 : Entails.eval a c6991 := derived6991 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9213 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, false), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9212, some c9208, some c9173, some c7129, some c9179, some c9181, some c4760, some c5489, some c5607, some c7010, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9213 : lratChecker f9213 p9213 = .success := by decide +kernel
theorem unsat9213 : Unsatisfiable (PosFin 65) f9213 := by
  apply lratCheckerSound f9213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9213
  · intro a ha; simp [p9213] at ha; subst a; trivial
  · exact checked9213
theorem derived9213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9213 := by
  apply localUnsat_implies_entails f9213 [c9212, c9208, c9173, c7129, c9179, c9181, c4760, c5489, c5607, c7010] c9213 unsat9213 (by rfl) a
  have h0 : Entails.eval a c9212 := derived9212 a h
  have h1 : Entails.eval a c9208 := derived9208 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9179 := derived9179 a h
  have h5 : Entails.eval a c9181 := derived9181 a h
  have h6 : Entails.eval a c4760 := h 4759 (by decide)
  have h7 : Entails.eval a c5489 := h 5488 (by decide)
  have h8 : Entails.eval a c5607 := h 5606 (by decide)
  have h9 : Entails.eval a c7010 := derived7010 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9214 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9212, some c9198, some c9173, some c5481, some c5486, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9214 : lratChecker f9214 p9214 = .success := by decide +kernel
theorem unsat9214 : Unsatisfiable (PosFin 65) f9214 := by
  apply lratCheckerSound f9214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9214
  · intro a ha; simp [p9214] at ha; subst a; trivial
  · exact checked9214
theorem derived9214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9214 := by
  apply localUnsat_implies_entails f9214 [c9212, c9198, c9173, c5481, c5486] c9214 unsat9214 (by rfl) a
  have h0 : Entails.eval a c9212 := derived9212 a h
  have h1 : Entails.eval a c9198 := derived9198 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c5481 := h 5480 (by decide)
  have h4 : Entails.eval a c5486 := h 5485 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9215 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9212, some c9208, some c7129, some c4767, some c6927, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9215 : lratChecker f9215 p9215 = .success := by decide +kernel
theorem unsat9215 : Unsatisfiable (PosFin 65) f9215 := by
  apply lratCheckerSound f9215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9215
  · intro a ha; simp [p9215] at ha; subst a; trivial
  · exact checked9215
theorem derived9215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9215 := by
  apply localUnsat_implies_entails f9215 [c9212, c9208, c7129, c4767, c6927] c9215 unsat9215 (by rfl) a
  have h0 : Entails.eval a c9212 := derived9212 a h
  have h1 : Entails.eval a c9208 := derived9208 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c4767 := h 4766 (by decide)
  have h4 : Entails.eval a c6927 := derived6927 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9216 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9215, some c9213, some c9214, some c5261, some c4712, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9216 : lratChecker f9216 p9216 = .success := by decide +kernel
theorem unsat9216 : Unsatisfiable (PosFin 65) f9216 := by
  apply lratCheckerSound f9216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9216
  · intro a ha; simp [p9216] at ha; subst a; trivial
  · exact checked9216
theorem derived9216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9216 := by
  apply localUnsat_implies_entails f9216 [c9215, c9213, c9214, c5261, c4712] c9216 unsat9216 (by rfl) a
  have h0 : Entails.eval a c9215 := derived9215 a h
  have h1 : Entails.eval a c9213 := derived9213 a h
  have h2 : Entails.eval a c9214 := derived9214 a h
  have h3 : Entails.eval a c5261 := h 5260 (by decide)
  have h4 : Entails.eval a c4712 := h 4711 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9217 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9212, some c9208, some c9216, some c4850, some c6908, some c4655, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9217 : lratChecker f9217 p9217 = .success := by decide +kernel
theorem unsat9217 : Unsatisfiable (PosFin 65) f9217 := by
  apply lratCheckerSound f9217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9217
  · intro a ha; simp [p9217] at ha; subst a; trivial
  · exact checked9217
theorem derived9217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9217 := by
  apply localUnsat_implies_entails f9217 [c9212, c9208, c9216, c4850, c6908, c4655] c9217 unsat9217 (by rfl) a
  have h0 : Entails.eval a c9212 := derived9212 a h
  have h1 : Entails.eval a c9208 := derived9208 a h
  have h2 : Entails.eval a c9216 := derived9216 a h
  have h3 : Entails.eval a c4850 := h 4849 (by decide)
  have h4 : Entails.eval a c6908 := derived6908 a h
  have h5 : Entails.eval a c4655 := h 4654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9218 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9208, some c9198, some c9173, some c7129, some c9215, some c9217, some c5900, some c5039, some c5033, some c5031, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9218 : lratChecker f9218 p9218 = .success := by decide +kernel
theorem unsat9218 : Unsatisfiable (PosFin 65) f9218 := by
  apply lratCheckerSound f9218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9218
  · intro a ha; simp [p9218] at ha; subst a; trivial
  · exact checked9218
theorem derived9218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9218 := by
  apply localUnsat_implies_entails f9218 [c9208, c9198, c9173, c7129, c9215, c9217, c5900, c5039, c5033, c5031] c9218 unsat9218 (by rfl) a
  have h0 : Entails.eval a c9208 := derived9208 a h
  have h1 : Entails.eval a c9198 := derived9198 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9215 := derived9215 a h
  have h5 : Entails.eval a c9217 := derived9217 a h
  have h6 : Entails.eval a c5900 := derived5900 a h
  have h7 : Entails.eval a c5039 := h 5038 (by decide)
  have h8 : Entails.eval a c5033 := h 5032 (by decide)
  have h9 : Entails.eval a c5031 := h 5030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9219 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c9208, some c5900, some c5033, some c5031, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9219 : lratChecker f9219 p9219 = .success := by decide +kernel
theorem unsat9219 : Unsatisfiable (PosFin 65) f9219 := by
  apply lratCheckerSound f9219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9219
  · intro a ha; simp [p9219] at ha; subst a; trivial
  · exact checked9219
theorem derived9219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9219 := by
  apply localUnsat_implies_entails f9219 [c9173, c7129, c9208, c5900, c5033, c5031] c9219 unsat9219 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9208 := derived9208 a h
  have h3 : Entails.eval a c5900 := derived5900 a h
  have h4 : Entails.eval a c5033 := h 5032 (by decide)
  have h5 : Entails.eval a c5031 := h 5030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9220 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c9208, some c5900, some c9218, some c9212, some c9219, some c7019, some c7016, some c6943, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9220 : lratChecker f9220 p9220 = .success := by decide +kernel
theorem unsat9220 : Unsatisfiable (PosFin 65) f9220 := by
  apply lratCheckerSound f9220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9220
  · intro a ha; simp [p9220] at ha; subst a; trivial
  · exact checked9220
theorem derived9220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9220 := by
  apply localUnsat_implies_entails f9220 [c9173, c7129, c9208, c5900, c9218, c9212, c9219, c7019, c7016, c6943] c9220 unsat9220 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9208 := derived9208 a h
  have h3 : Entails.eval a c5900 := derived5900 a h
  have h4 : Entails.eval a c9218 := derived9218 a h
  have h5 : Entails.eval a c9212 := derived9212 a h
  have h6 : Entails.eval a c9219 := derived9219 a h
  have h7 : Entails.eval a c7019 := derived7019 a h
  have h8 : Entails.eval a c7016 := derived7016 a h
  have h9 : Entails.eval a c6943 := derived6943 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9221 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9208, some c9198, some c9173, some c7129, some c9220, some c5250, some c5039, some c5522, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9221 : lratChecker f9221 p9221 = .success := by decide +kernel
theorem unsat9221 : Unsatisfiable (PosFin 65) f9221 := by
  apply lratCheckerSound f9221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9221
  · intro a ha; simp [p9221] at ha; subst a; trivial
  · exact checked9221
theorem derived9221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9221 := by
  apply localUnsat_implies_entails f9221 [c9208, c9198, c9173, c7129, c9220, c5250, c5039, c5522] c9221 unsat9221 (by rfl) a
  have h0 : Entails.eval a c9208 := derived9208 a h
  have h1 : Entails.eval a c9198 := derived9198 a h
  have h2 : Entails.eval a c9173 := derived9173 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9220 := derived9220 a h
  have h5 : Entails.eval a c5250 := h 5249 (by decide)
  have h6 : Entails.eval a c5039 := h 5038 (by decide)
  have h7 : Entails.eval a c5522 := h 5521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9222 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9221, some c9218, some c9198, some c9173, some c7129, some c4370, some c4949, some c4409, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9222 : lratChecker f9222 p9222 = .success := by decide +kernel
theorem unsat9222 : Unsatisfiable (PosFin 65) f9222 := by
  apply lratCheckerSound f9222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9222
  · intro a ha; simp [p9222] at ha; subst a; trivial
  · exact checked9222
theorem derived9222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9222 := by
  apply localUnsat_implies_entails f9222 [c9221, c9218, c9198, c9173, c7129, c4370, c4949, c4409] c9222 unsat9222 (by rfl) a
  have h0 : Entails.eval a c9221 := derived9221 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9198 := derived9198 a h
  have h3 : Entails.eval a c9173 := derived9173 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c4370 := h 4369 (by decide)
  have h6 : Entails.eval a c4949 := h 4948 (by decide)
  have h7 : Entails.eval a c4409 := h 4408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9223 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9222, some c9221, some c9218, some c9212, some c9208, some c9173, some c7129, some c6867, some c4377, some c6780, some c6793, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9223 : lratChecker f9223 p9223 = .success := by decide +kernel
theorem unsat9223 : Unsatisfiable (PosFin 65) f9223 := by
  apply lratCheckerSound f9223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9223
  · intro a ha; simp [p9223] at ha; subst a; trivial
  · exact checked9223
theorem derived9223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9223 := by
  apply localUnsat_implies_entails f9223 [c9222, c9221, c9218, c9212, c9208, c9173, c7129, c6867, c4377, c6780, c6793] c9223 unsat9223 (by rfl) a
  have h0 : Entails.eval a c9222 := derived9222 a h
  have h1 : Entails.eval a c9221 := derived9221 a h
  have h2 : Entails.eval a c9218 := derived9218 a h
  have h3 : Entails.eval a c9212 := derived9212 a h
  have h4 : Entails.eval a c9208 := derived9208 a h
  have h5 : Entails.eval a c9173 := derived9173 a h
  have h6 : Entails.eval a c7129 := derived7129 a h
  have h7 : Entails.eval a c6867 := derived6867 a h
  have h8 : Entails.eval a c4377 := h 4376 (by decide)
  have h9 : Entails.eval a c6780 := derived6780 a h
  have h10 : Entails.eval a c6793 := derived6793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9224 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6874, some c6816, some c6869, some c6863, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p9224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9224 : lratChecker f9224 p9224 = .success := by decide +kernel
theorem unsat9224 : Unsatisfiable (PosFin 65) f9224 := by
  apply lratCheckerSound f9224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9224
  · intro a ha; simp [p9224] at ha; subst a; trivial
  · exact checked9224
theorem derived9224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9224 := by
  apply localUnsat_implies_entails f9224 [c6874, c6816, c6869, c6863] c9224 unsat9224 (by rfl) a
  have h0 : Entails.eval a c6874 := derived6874 a h
  have h1 : Entails.eval a c6816 := derived6816 a h
  have h2 : Entails.eval a c6869 := derived6869 a h
  have h3 : Entails.eval a c6863 := derived6863 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9225 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9212, some c9221, some c9222, some c9223, some c9224, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9225 : lratChecker f9225 p9225 = .success := by decide +kernel
theorem unsat9225 : Unsatisfiable (PosFin 65) f9225 := by
  apply lratCheckerSound f9225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9225
  · intro a ha; simp [p9225] at ha; subst a; trivial
  · exact checked9225
theorem derived9225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9225 := by
  apply localUnsat_implies_entails f9225 [c9212, c9221, c9222, c9223, c9224] c9225 unsat9225 (by rfl) a
  have h0 : Entails.eval a c9212 := derived9212 a h
  have h1 : Entails.eval a c9221 := derived9221 a h
  have h2 : Entails.eval a c9222 := derived9222 a h
  have h3 : Entails.eval a c9223 := derived9223 a h
  have h4 : Entails.eval a c9224 := derived9224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9226 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨37, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9225, some c9212, some c9208, some c9173, some c7129, some c9224, some c4619, some c4597, some c4607, some c4609, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9226 : lratChecker f9226 p9226 = .success := by decide +kernel
theorem unsat9226 : Unsatisfiable (PosFin 65) f9226 := by
  apply lratCheckerSound f9226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9226
  · intro a ha; simp [p9226] at ha; subst a; trivial
  · exact checked9226
theorem derived9226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9226 := by
  apply localUnsat_implies_entails f9226 [c9225, c9212, c9208, c9173, c7129, c9224, c4619, c4597, c4607, c4609] c9226 unsat9226 (by rfl) a
  have h0 : Entails.eval a c9225 := derived9225 a h
  have h1 : Entails.eval a c9212 := derived9212 a h
  have h2 : Entails.eval a c9208 := derived9208 a h
  have h3 : Entails.eval a c9173 := derived9173 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c9224 := derived9224 a h
  have h6 : Entails.eval a c4619 := h 4618 (by decide)
  have h7 : Entails.eval a c4597 := h 4596 (by decide)
  have h8 : Entails.eval a c4607 := h 4606 (by decide)
  have h9 : Entails.eval a c4609 := h 4608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9227 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9225, some c9208, some c9198, some c9173, some c7129, some c9226, some c5854, some c4615, some c4409, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9227 : lratChecker f9227 p9227 = .success := by decide +kernel
theorem unsat9227 : Unsatisfiable (PosFin 65) f9227 := by
  apply lratCheckerSound f9227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9227
  · intro a ha; simp [p9227] at ha; subst a; trivial
  · exact checked9227
theorem derived9227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9227 := by
  apply localUnsat_implies_entails f9227 [c9225, c9208, c9198, c9173, c7129, c9226, c5854, c4615, c4409] c9227 unsat9227 (by rfl) a
  have h0 : Entails.eval a c9225 := derived9225 a h
  have h1 : Entails.eval a c9208 := derived9208 a h
  have h2 : Entails.eval a c9198 := derived9198 a h
  have h3 : Entails.eval a c9173 := derived9173 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c9226 := derived9226 a h
  have h6 : Entails.eval a c5854 := h 5853 (by decide)
  have h7 : Entails.eval a c4615 := h 4614 (by decide)
  have h8 : Entails.eval a c4409 := h 4408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9228 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9173, some c9198, some c9208, some c9225, some c9227, some c5197, some c5186, some c5193, some c5182, some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9228 : lratChecker f9228 p9228 = .success := by decide +kernel
theorem unsat9228 : Unsatisfiable (PosFin 65) f9228 := by
  apply lratCheckerSound f9228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9228
  · intro a ha; simp [p9228] at ha; subst a; trivial
  · exact checked9228
theorem derived9228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9228 := by
  apply localUnsat_implies_entails f9228 [c7129, c9173, c9198, c9208, c9225, c9227, c5197, c5186, c5193, c5182] c9228 unsat9228 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9173 := derived9173 a h
  have h2 : Entails.eval a c9198 := derived9198 a h
  have h3 : Entails.eval a c9208 := derived9208 a h
  have h4 : Entails.eval a c9225 := derived9225 a h
  have h5 : Entails.eval a c9227 := derived9227 a h
  have h6 : Entails.eval a c5197 := h 5196 (by decide)
  have h7 : Entails.eval a c5186 := h 5185 (by decide)
  have h8 : Entails.eval a c5193 := h 5192 (by decide)
  have h9 : Entails.eval a c5182 := h 5181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9229 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c8670, some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p9229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9229 : lratChecker f9229 p9229 = .success := by decide +kernel
theorem unsat9229 : Unsatisfiable (PosFin 65) f9229 := by
  apply lratCheckerSound f9229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9229
  · intro a ha; simp [p9229] at ha; subst a; trivial
  · exact checked9229
theorem derived9229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9229 := by
  apply localUnsat_implies_entails f9229 [c9228, c8670] c9229 unsat9229 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c8670 := derived8670 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9230 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c8840, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9230 : lratChecker f9230 p9230 = .success := by decide +kernel
theorem unsat9230 : Unsatisfiable (PosFin 65) f9230 := by
  apply lratCheckerSound f9230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9230
  · intro a ha; simp [p9230] at ha; subst a; trivial
  · exact checked9230
theorem derived9230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9230 := by
  apply localUnsat_implies_entails f9230 [c9228, c8840] c9230 unsat9230 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9231 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c5900, some c5186, some c5182, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9231 : lratChecker f9231 p9231 = .success := by decide +kernel
theorem unsat9231 : Unsatisfiable (PosFin 65) f9231 := by
  apply lratCheckerSound f9231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9231
  · intro a ha; simp [p9231] at ha; subst a; trivial
  · exact checked9231
theorem derived9231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9231 := by
  apply localUnsat_implies_entails f9231 [c9229, c5900, c5186, c5182] c9231 unsat9231 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c5900 := derived5900 a h
  have h2 : Entails.eval a c5186 := h 5185 (by decide)
  have h3 : Entails.eval a c5182 := h 5181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9232 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9231, some c5182, some c5188, some c5174, some c9022, some c5175, some c6895, some c6879, some c6892, some c5180, some c7007, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9232 : lratChecker f9232 p9232 = .success := by decide +kernel
theorem unsat9232 : Unsatisfiable (PosFin 65) f9232 := by
  apply lratCheckerSound f9232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9232
  · intro a ha; simp [p9232] at ha; subst a; trivial
  · exact checked9232
theorem derived9232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9232 := by
  apply localUnsat_implies_entails f9232 [c9229, c9231, c5182, c5188, c5174, c9022, c5175, c6895, c6879, c6892, c5180, c7007] c9232 unsat9232 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9231 := derived9231 a h
  have h2 : Entails.eval a c5182 := h 5181 (by decide)
  have h3 : Entails.eval a c5188 := h 5187 (by decide)
  have h4 : Entails.eval a c5174 := h 5173 (by decide)
  have h5 : Entails.eval a c9022 := derived9022 a h
  have h6 : Entails.eval a c5175 := h 5174 (by decide)
  have h7 : Entails.eval a c6895 := derived6895 a h
  have h8 : Entails.eval a c6879 := derived6879 a h
  have h9 : Entails.eval a c6892 := derived6892 a h
  have h10 : Entails.eval a c5180 := h 5179 (by decide)
  have h11 : Entails.eval a c7007 := derived7007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9233 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9231, some c9232, some c5177, some c5195, some c5176, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9233 : lratChecker f9233 p9233 = .success := by decide +kernel
theorem unsat9233 : Unsatisfiable (PosFin 65) f9233 := by
  apply lratCheckerSound f9233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9233
  · intro a ha; simp [p9233] at ha; subst a; trivial
  · exact checked9233
theorem derived9233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9233 := by
  apply localUnsat_implies_entails f9233 [c9229, c9231, c9232, c5177, c5195, c5176] c9233 unsat9233 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9231 := derived9231 a h
  have h2 : Entails.eval a c9232 := derived9232 a h
  have h3 : Entails.eval a c5177 := h 5176 (by decide)
  have h4 : Entails.eval a c5195 := h 5194 (by decide)
  have h5 : Entails.eval a c5176 := h 5175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9234 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9233, some c6962, some c6972, some c5621, some c6895, some c6879, some c6892, some c5431, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9234 : lratChecker f9234 p9234 = .success := by decide +kernel
theorem unsat9234 : Unsatisfiable (PosFin 65) f9234 := by
  apply lratCheckerSound f9234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9234
  · intro a ha; simp [p9234] at ha; subst a; trivial
  · exact checked9234
theorem derived9234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9234 := by
  apply localUnsat_implies_entails f9234 [c9228, c9233, c6962, c6972, c5621, c6895, c6879, c6892, c5431] c9234 unsat9234 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9233 := derived9233 a h
  have h2 : Entails.eval a c6962 := derived6962 a h
  have h3 : Entails.eval a c6972 := derived6972 a h
  have h4 : Entails.eval a c5621 := h 5620 (by decide)
  have h5 : Entails.eval a c6895 := derived6895 a h
  have h6 : Entails.eval a c6879 := derived6879 a h
  have h7 : Entails.eval a c6892 := derived6892 a h
  have h8 : Entails.eval a c5431 := h 5430 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9235 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c5812, some c4132, some c4444, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p9235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9235 : lratChecker f9235 p9235 = .success := by decide +kernel
theorem unsat9235 : Unsatisfiable (PosFin 65) f9235 := by
  apply lratCheckerSound f9235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9235
  · intro a ha; simp [p9235] at ha; subst a; trivial
  · exact checked9235
theorem derived9235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9235 := by
  apply localUnsat_implies_entails f9235 [c9229, c5812, c4132, c4444] c9235 unsat9235 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c5812 := h 5811 (by decide)
  have h2 : Entails.eval a c4132 := h 4131 (by decide)
  have h3 : Entails.eval a c4444 := h 4443 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9236 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c5343, some c6880, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p9236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9236 : lratChecker f9236 p9236 = .success := by decide +kernel
theorem unsat9236 : Unsatisfiable (PosFin 65) f9236 := by
  apply lratCheckerSound f9236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9236
  · intro a ha; simp [p9236] at ha; subst a; trivial
  · exact checked9236
theorem derived9236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9236 := by
  apply localUnsat_implies_entails f9236 [c9229, c5343, c6880] c9236 unsat9236 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c5343 := h 5342 (by decide)
  have h2 : Entails.eval a c6880 := derived6880 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9237 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9233, some c9234, some c5052, some c4178, some c9235, some c4623, some c4281, some c4444, some c5862, some c4954, some c9236, some c5753, some c6974, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9237 : lratChecker f9237 p9237 = .success := by decide +kernel
theorem unsat9237 : Unsatisfiable (PosFin 65) f9237 := by
  apply lratCheckerSound f9237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9237
  · intro a ha; simp [p9237] at ha; subst a; trivial
  · exact checked9237
theorem derived9237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9237 := by
  apply localUnsat_implies_entails f9237 [c9229, c9233, c9234, c5052, c4178, c9235, c4623, c4281, c4444, c5862, c4954, c9236, c5753, c6974] c9237 unsat9237 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9233 := derived9233 a h
  have h2 : Entails.eval a c9234 := derived9234 a h
  have h3 : Entails.eval a c5052 := h 5051 (by decide)
  have h4 : Entails.eval a c4178 := h 4177 (by decide)
  have h5 : Entails.eval a c9235 := derived9235 a h
  have h6 : Entails.eval a c4623 := h 4622 (by decide)
  have h7 : Entails.eval a c4281 := h 4280 (by decide)
  have h8 : Entails.eval a c4444 := h 4443 (by decide)
  have h9 : Entails.eval a c5862 := h 5861 (by decide)
  have h10 : Entails.eval a c4954 := h 4953 (by decide)
  have h11 : Entails.eval a c9236 := derived9236 a h
  have h12 : Entails.eval a c5753 := h 5752 (by decide)
  have h13 : Entails.eval a c6974 := derived6974 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9238 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨62, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c6974, some c5112, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9238 : lratChecker f9238 p9238 = .success := by decide +kernel
theorem unsat9238 : Unsatisfiable (PosFin 65) f9238 := by
  apply lratCheckerSound f9238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9238
  · intro a ha; simp [p9238] at ha; subst a; trivial
  · exact checked9238
theorem derived9238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9238 := by
  apply localUnsat_implies_entails f9238 [c9229, c6974, c5112] c9238 unsat9238 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c6974 := derived6974 a h
  have h2 : Entails.eval a c5112 := h 5111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9239 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨62, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9237, some c6964, some c9233, some c9238, some c5622, some c5619, some c9236, some c6952, some c6897, some c6935, some c4917, some c3718, some c5869, some c3869, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9239 : lratChecker f9239 p9239 = .success := by decide +kernel
theorem unsat9239 : Unsatisfiable (PosFin 65) f9239 := by
  apply lratCheckerSound f9239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9239
  · intro a ha; simp [p9239] at ha; subst a; trivial
  · exact checked9239
theorem derived9239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9239 := by
  apply localUnsat_implies_entails f9239 [c9229, c9237, c6964, c9233, c9238, c5622, c5619, c9236, c6952, c6897, c6935, c4917, c3718, c5869, c3869] c9239 unsat9239 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9237 := derived9237 a h
  have h2 : Entails.eval a c6964 := derived6964 a h
  have h3 : Entails.eval a c9233 := derived9233 a h
  have h4 : Entails.eval a c9238 := derived9238 a h
  have h5 : Entails.eval a c5622 := h 5621 (by decide)
  have h6 : Entails.eval a c5619 := h 5618 (by decide)
  have h7 : Entails.eval a c9236 := derived9236 a h
  have h8 : Entails.eval a c6952 := derived6952 a h
  have h9 : Entails.eval a c6897 := derived6897 a h
  have h10 : Entails.eval a c6935 := derived6935 a h
  have h11 : Entails.eval a c4917 := h 4916 (by decide)
  have h12 : Entails.eval a c3718 := h 3717 (by decide)
  have h13 : Entails.eval a c5869 := h 5868 (by decide)
  have h14 : Entails.eval a c3869 := h 3868 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9240 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9239, some c6972, some c6895, some c6892, some c7044, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9240 : lratChecker f9240 p9240 = .success := by decide +kernel
theorem unsat9240 : Unsatisfiable (PosFin 65) f9240 := by
  apply lratCheckerSound f9240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9240
  · intro a ha; simp [p9240] at ha; subst a; trivial
  · exact checked9240
theorem derived9240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9240 := by
  apply localUnsat_implies_entails f9240 [c9239, c6972, c6895, c6892, c7044] c9240 unsat9240 (by rfl) a
  have h0 : Entails.eval a c9239 := derived9239 a h
  have h1 : Entails.eval a c6972 := derived6972 a h
  have h2 : Entails.eval a c6895 := derived6895 a h
  have h3 : Entails.eval a c6892 := derived6892 a h
  have h4 : Entails.eval a c7044 := derived7044 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9241 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6972, some c6894, some c6891, some c7044, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9241 : lratChecker f9241 p9241 = .success := by decide +kernel
theorem unsat9241 : Unsatisfiable (PosFin 65) f9241 := by
  apply lratCheckerSound f9241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9241
  · intro a ha; simp [p9241] at ha; subst a; trivial
  · exact checked9241
theorem derived9241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9241 := by
  apply localUnsat_implies_entails f9241 [c6972, c6894, c6891, c7044] c9241 unsat9241 (by rfl) a
  have h0 : Entails.eval a c6972 := derived6972 a h
  have h1 : Entails.eval a c6894 := derived6894 a h
  have h2 : Entails.eval a c6891 := derived6891 a h
  have h3 : Entails.eval a c7044 := derived7044 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9242 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c5812, some c5818, some c5816, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9242 : lratChecker f9242 p9242 = .success := by decide +kernel
theorem unsat9242 : Unsatisfiable (PosFin 65) f9242 := by
  apply lratCheckerSound f9242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9242
  · intro a ha; simp [p9242] at ha; subst a; trivial
  · exact checked9242
theorem derived9242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9242 := by
  apply localUnsat_implies_entails f9242 [c9229, c5812, c5818, c5816] c9242 unsat9242 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c5812 := h 5811 (by decide)
  have h2 : Entails.eval a c5818 := h 5817 (by decide)
  have h3 : Entails.eval a c5816 := h 5815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9243 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9240, some c9241, some c9242, some c9233, some c6964, some c4183, some c6882, some c4134, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9243 : lratChecker f9243 p9243 = .success := by decide +kernel
theorem unsat9243 : Unsatisfiable (PosFin 65) f9243 := by
  apply lratCheckerSound f9243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9243
  · intro a ha; simp [p9243] at ha; subst a; trivial
  · exact checked9243
theorem derived9243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9243 := by
  apply localUnsat_implies_entails f9243 [c9240, c9241, c9242, c9233, c6964, c4183, c6882, c4134] c9243 unsat9243 (by rfl) a
  have h0 : Entails.eval a c9240 := derived9240 a h
  have h1 : Entails.eval a c9241 := derived9241 a h
  have h2 : Entails.eval a c9242 := derived9242 a h
  have h3 : Entails.eval a c9233 := derived9233 a h
  have h4 : Entails.eval a c6964 := derived6964 a h
  have h5 : Entails.eval a c4183 := h 4182 (by decide)
  have h6 : Entails.eval a c6882 := derived6882 a h
  have h7 : Entails.eval a c4134 := h 4133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9244 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9241, some c9240, some c9233, some c9242, some c5745, some c9243, some c5076, some c4202, some c9235, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9244 : lratChecker f9244 p9244 = .success := by decide +kernel
theorem unsat9244 : Unsatisfiable (PosFin 65) f9244 := by
  apply lratCheckerSound f9244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9244
  · intro a ha; simp [p9244] at ha; subst a; trivial
  · exact checked9244
theorem derived9244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9244 := by
  apply localUnsat_implies_entails f9244 [c9229, c9241, c9240, c9233, c9242, c5745, c9243, c5076, c4202, c9235] c9244 unsat9244 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9241 := derived9241 a h
  have h2 : Entails.eval a c9240 := derived9240 a h
  have h3 : Entails.eval a c9233 := derived9233 a h
  have h4 : Entails.eval a c9242 := derived9242 a h
  have h5 : Entails.eval a c5745 := h 5744 (by decide)
  have h6 : Entails.eval a c9243 := derived9243 a h
  have h7 : Entails.eval a c5076 := h 5075 (by decide)
  have h8 : Entails.eval a c4202 := h 4201 (by decide)
  have h9 : Entails.eval a c9235 := derived9235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9245 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨24, by decide⟩, true), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false), (⟨57, by decide⟩, false), (⟨61, by decide⟩, false), (⟨59, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c2976, some c3382, some c3083, some c2897, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p9245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9245 : lratChecker f9245 p9245 = .success := by decide +kernel
theorem unsat9245 : Unsatisfiable (PosFin 65) f9245 := by
  apply lratCheckerSound f9245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9245
  · intro a ha; simp [p9245] at ha; subst a; trivial
  · exact checked9245
theorem derived9245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9245 := by
  apply localUnsat_implies_entails f9245 [c9228, c2976, c3382, c3083, c2897] c9245 unsat9245 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c2976 := h 2975 (by decide)
  have h2 : Entails.eval a c3382 := h 3381 (by decide)
  have h3 : Entails.eval a c3083 := h 3082 (by decide)
  have h4 : Entails.eval a c2897 := h 2896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9246 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨42, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨57, by decide⟩, false), (⟨61, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨62, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c2690, some c2684, some c2691, some c3123, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p9246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9246 : lratChecker f9246 p9246 = .success := by decide +kernel
theorem unsat9246 : Unsatisfiable (PosFin 65) f9246 := by
  apply lratCheckerSound f9246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9246
  · intro a ha; simp [p9246] at ha; subst a; trivial
  · exact checked9246
theorem derived9246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9246 := by
  apply localUnsat_implies_entails f9246 [c9229, c2690, c2684, c2691, c3123] c9246 unsat9246 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c2690 := h 2689 (by decide)
  have h2 : Entails.eval a c2684 := h 2683 (by decide)
  have h3 : Entails.eval a c2691 := h 2690 (by decide)
  have h4 : Entails.eval a c3123 := h 3122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9247 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨38, by decide⟩, true), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false), (⟨57, by decide⟩, false), (⟨61, by decide⟩, false), (⟨59, by decide⟩, false), (⟨55, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9245, some c2951, some c2968, some c3379, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p9247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9247 : lratChecker f9247 p9247 = .success := by decide +kernel
theorem unsat9247 : Unsatisfiable (PosFin 65) f9247 := by
  apply lratCheckerSound f9247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9247
  · intro a ha; simp [p9247] at ha; subst a; trivial
  · exact checked9247
theorem derived9247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9247 := by
  apply localUnsat_implies_entails f9247 [c9229, c9245, c2951, c2968, c3379] c9247 unsat9247 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9245 := derived9245 a h
  have h2 : Entails.eval a c2951 := h 2950 (by decide)
  have h3 : Entails.eval a c2968 := h 2967 (by decide)
  have h4 : Entails.eval a c3379 := h 3378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9248 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨17, by decide⟩, true), (⟨38, by decide⟩, true), (⟨40, by decide⟩, true), (⟨57, by decide⟩, false), (⟨59, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c8996, some c2933, some c3268, some c3396, some c3292, some c3203, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9248 : lratChecker f9248 p9248 = .success := by decide +kernel
theorem unsat9248 : Unsatisfiable (PosFin 65) f9248 := by
  apply lratCheckerSound f9248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9248
  · intro a ha; simp [p9248] at ha; subst a; trivial
  · exact checked9248
theorem derived9248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9248 := by
  apply localUnsat_implies_entails f9248 [c9228, c9229, c8996, c2933, c3268, c3396, c3292, c3203] c9248 unsat9248 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c8996 := derived8996 a h
  have h3 : Entails.eval a c2933 := h 2932 (by decide)
  have h4 : Entails.eval a c3268 := h 3267 (by decide)
  have h5 : Entails.eval a c3396 := h 3395 (by decide)
  have h6 : Entails.eval a c3292 := h 3291 (by decide)
  have h7 : Entails.eval a c3203 := h 3202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9249 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨61, by decide⟩, false), (⟨44, by decide⟩, true), (⟨59, by decide⟩, false), (⟨55, by decide⟩, false), (⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c5076, some c3794, some c4202, some c3985, some c4444, some c5862, some c4827, some c5272, some c9246, some c9247, some c9248, some c2942, some c3021, some c3327, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9249 : lratChecker f9249 p9249 = .success := by decide +kernel
theorem unsat9249 : Unsatisfiable (PosFin 65) f9249 := by
  apply lratCheckerSound f9249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9249
  · intro a ha; simp [p9249] at ha; subst a; trivial
  · exact checked9249
theorem derived9249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9249 := by
  apply localUnsat_implies_entails f9249 [c9229, c9228, c5076, c3794, c4202, c3985, c4444, c5862, c4827, c5272, c9246, c9247, c9248, c2942, c3021, c3327] c9249 unsat9249 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c5076 := h 5075 (by decide)
  have h3 : Entails.eval a c3794 := h 3793 (by decide)
  have h4 : Entails.eval a c4202 := h 4201 (by decide)
  have h5 : Entails.eval a c3985 := h 3984 (by decide)
  have h6 : Entails.eval a c4444 := h 4443 (by decide)
  have h7 : Entails.eval a c5862 := h 5861 (by decide)
  have h8 : Entails.eval a c4827 := h 4826 (by decide)
  have h9 : Entails.eval a c5272 := h 5271 (by decide)
  have h10 : Entails.eval a c9246 := derived9246 a h
  have h11 : Entails.eval a c9247 := derived9247 a h
  have h12 : Entails.eval a c9248 := derived9248 a h
  have h13 : Entails.eval a c2942 := h 2941 (by decide)
  have h14 : Entails.eval a c3021 := h 3020 (by decide)
  have h15 : Entails.eval a c3327 := h 3326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9250 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2942, some c2975, some c3026, some c3326, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9250 : lratChecker f9250 p9250 = .success := by decide +kernel
theorem unsat9250 : Unsatisfiable (PosFin 65) f9250 := by
  apply lratCheckerSound f9250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9250
  · intro a ha; simp [p9250] at ha; subst a; trivial
  · exact checked9250
theorem derived9250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9250 := by
  apply localUnsat_implies_entails f9250 [c2942, c2975, c3026, c3326] c9250 unsat9250 (by rfl) a
  have h0 : Entails.eval a c2942 := h 2941 (by decide)
  have h1 : Entails.eval a c2975 := h 2974 (by decide)
  have h2 : Entails.eval a c3026 := h 3025 (by decide)
  have h3 : Entails.eval a c3326 := h 3325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9251 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨40, by decide⟩, true), (⟨57, by decide⟩, true), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, true), (⟨62, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c5745, some c5743, some c2856, some c2893, some c2876, some c3059, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9251 : lratChecker f9251 p9251 = .success := by decide +kernel
theorem unsat9251 : Unsatisfiable (PosFin 65) f9251 := by
  apply lratCheckerSound f9251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9251
  · intro a ha; simp [p9251] at ha; subst a; trivial
  · exact checked9251
theorem derived9251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9251 := by
  apply localUnsat_implies_entails f9251 [c9229, c9228, c5745, c5743, c2856, c2893, c2876, c3059] c9251 unsat9251 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c5745 := h 5744 (by decide)
  have h3 : Entails.eval a c5743 := h 5742 (by decide)
  have h4 : Entails.eval a c2856 := h 2855 (by decide)
  have h5 : Entails.eval a c2893 := h 2892 (by decide)
  have h6 : Entails.eval a c2876 := h 2875 (by decide)
  have h7 : Entails.eval a c3059 := h 3058 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9252 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9250, some c6727, some c8996, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9252 : lratChecker f9252 p9252 = .success := by decide +kernel
theorem unsat9252 : Unsatisfiable (PosFin 65) f9252 := by
  apply lratCheckerSound f9252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9252
  · intro a ha; simp [p9252] at ha; subst a; trivial
  · exact checked9252
theorem derived9252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9252 := by
  apply localUnsat_implies_entails f9252 [c9228, c9250, c6727, c8996] c9252 unsat9252 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9250 := derived9250 a h
  have h2 : Entails.eval a c6727 := derived6727 a h
  have h3 : Entails.eval a c8996 := derived8996 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9253 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9244, some c9241, some c6896, some c4531, some c4541, some c4536, some c4542, some c9240, some c9177, some c9233, some c5745, some c5743, some c5740, some c9249, some c6964, some c4183, some c3770, some c7023, some c3975, some c9251, some c9252, some c2693, some c2689, some c2827, some c3121, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked9253 : lratChecker f9253 p9253 = .success := by decide +kernel
theorem unsat9253 : Unsatisfiable (PosFin 65) f9253 := by
  apply lratCheckerSound f9253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9253
  · intro a ha; simp [p9253] at ha; subst a; trivial
  · exact checked9253
theorem derived9253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9253 := by
  apply localUnsat_implies_entails f9253 [c9229, c9244, c9241, c6896, c4531, c4541, c4536, c4542, c9240, c9177, c9233, c5745, c5743, c5740, c9249, c6964, c4183, c3770, c7023, c3975, c9251, c9252, c2693, c2689, c2827, c3121] c9253 unsat9253 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9244 := derived9244 a h
  have h2 : Entails.eval a c9241 := derived9241 a h
  have h3 : Entails.eval a c6896 := derived6896 a h
  have h4 : Entails.eval a c4531 := h 4530 (by decide)
  have h5 : Entails.eval a c4541 := h 4540 (by decide)
  have h6 : Entails.eval a c4536 := h 4535 (by decide)
  have h7 : Entails.eval a c4542 := h 4541 (by decide)
  have h8 : Entails.eval a c9240 := derived9240 a h
  have h9 : Entails.eval a c9177 := derived9177 a h
  have h10 : Entails.eval a c9233 := derived9233 a h
  have h11 : Entails.eval a c5745 := h 5744 (by decide)
  have h12 : Entails.eval a c5743 := h 5742 (by decide)
  have h13 : Entails.eval a c5740 := h 5739 (by decide)
  have h14 : Entails.eval a c9249 := derived9249 a h
  have h15 : Entails.eval a c6964 := derived6964 a h
  have h16 : Entails.eval a c4183 := h 4182 (by decide)
  have h17 : Entails.eval a c3770 := h 3769 (by decide)
  have h18 : Entails.eval a c7023 := derived7023 a h
  have h19 : Entails.eval a c3975 := h 3974 (by decide)
  have h20 : Entails.eval a c9251 := derived9251 a h
  have h21 : Entails.eval a c9252 := derived9252 a h
  have h22 : Entails.eval a c2693 := h 2692 (by decide)
  have h23 : Entails.eval a c2689 := h 2688 (by decide)
  have h24 : Entails.eval a c2827 := h 2826 (by decide)
  have h25 : Entails.eval a c3121 := h 3120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9254 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨47, by decide⟩, true), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6964, some c3876, some c3744, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9254 : lratChecker f9254 p9254 = .success := by decide +kernel
theorem unsat9254 : Unsatisfiable (PosFin 65) f9254 := by
  apply lratCheckerSound f9254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9254
  · intro a ha; simp [p9254] at ha; subst a; trivial
  · exact checked9254
theorem derived9254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9254 := by
  apply localUnsat_implies_entails f9254 [c6964, c3876, c3744] c9254 unsat9254 (by rfl) a
  have h0 : Entails.eval a c6964 := derived6964 a h
  have h1 : Entails.eval a c3876 := h 3875 (by decide)
  have h2 : Entails.eval a c3744 := h 3743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9255 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9241, some c9240, some c9233, some c9244, some c4536, some c6896, some c4531, some c4542, some c4541, some c4545, some c9253, some c9254, some c5076, some c3794, some c3877, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9255 : lratChecker f9255 p9255 = .success := by decide +kernel
theorem unsat9255 : Unsatisfiable (PosFin 65) f9255 := by
  apply lratCheckerSound f9255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9255
  · intro a ha; simp [p9255] at ha; subst a; trivial
  · exact checked9255
theorem derived9255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9255 := by
  apply localUnsat_implies_entails f9255 [c9229, c9228, c9241, c9240, c9233, c9244, c4536, c6896, c4531, c4542, c4541, c4545, c9253, c9254, c5076, c3794, c3877] c9255 unsat9255 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9241 := derived9241 a h
  have h3 : Entails.eval a c9240 := derived9240 a h
  have h4 : Entails.eval a c9233 := derived9233 a h
  have h5 : Entails.eval a c9244 := derived9244 a h
  have h6 : Entails.eval a c4536 := h 4535 (by decide)
  have h7 : Entails.eval a c6896 := derived6896 a h
  have h8 : Entails.eval a c4531 := h 4530 (by decide)
  have h9 : Entails.eval a c4542 := h 4541 (by decide)
  have h10 : Entails.eval a c4541 := h 4540 (by decide)
  have h11 : Entails.eval a c4545 := h 4544 (by decide)
  have h12 : Entails.eval a c9253 := derived9253 a h
  have h13 : Entails.eval a c9254 := derived9254 a h
  have h14 : Entails.eval a c5076 := h 5075 (by decide)
  have h15 : Entails.eval a c3794 := h 3793 (by decide)
  have h16 : Entails.eval a c3877 := h 3876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9256 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨17, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, false), (⟨55, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3003, some c2928, some c2954, some c3320, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p9256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9256 : lratChecker f9256 p9256 = .success := by decide +kernel
theorem unsat9256 : Unsatisfiable (PosFin 65) f9256 := by
  apply lratCheckerSound f9256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9256
  · intro a ha; simp [p9256] at ha; subst a; trivial
  · exact checked9256
theorem derived9256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9256 := by
  apply localUnsat_implies_entails f9256 [c3003, c2928, c2954, c3320] c9256 unsat9256 (by rfl) a
  have h0 : Entails.eval a c3003 := h 3002 (by decide)
  have h1 : Entails.eval a c2928 := h 2927 (by decide)
  have h2 : Entails.eval a c2954 := h 2953 (by decide)
  have h3 : Entails.eval a c3320 := h 3319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9257 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c5112, some c5120, some c5118, some c5076, some c3794, some c4202, some c3879, some c3431, some c5964, some c9235, some c5862, some c4825, some c9177, some c9246, some c9256, some c2892, some c2858, some c2875, some c3053, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9257 : lratChecker f9257 p9257 = .success := by decide +kernel
theorem unsat9257 : Unsatisfiable (PosFin 65) f9257 := by
  apply lratCheckerSound f9257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9257
  · intro a ha; simp [p9257] at ha; subst a; trivial
  · exact checked9257
theorem derived9257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9257 := by
  apply localUnsat_implies_entails f9257 [c9228, c9229, c5112, c5120, c5118, c5076, c3794, c4202, c3879, c3431, c5964, c9235, c5862, c4825, c9177, c9246, c9256, c2892, c2858, c2875, c3053] c9257 unsat9257 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c5112 := h 5111 (by decide)
  have h3 : Entails.eval a c5120 := h 5119 (by decide)
  have h4 : Entails.eval a c5118 := h 5117 (by decide)
  have h5 : Entails.eval a c5076 := h 5075 (by decide)
  have h6 : Entails.eval a c3794 := h 3793 (by decide)
  have h7 : Entails.eval a c4202 := h 4201 (by decide)
  have h8 : Entails.eval a c3879 := h 3878 (by decide)
  have h9 : Entails.eval a c3431 := h 3430 (by decide)
  have h10 : Entails.eval a c5964 := derived5964 a h
  have h11 : Entails.eval a c9235 := derived9235 a h
  have h12 : Entails.eval a c5862 := h 5861 (by decide)
  have h13 : Entails.eval a c4825 := h 4824 (by decide)
  have h14 : Entails.eval a c9177 := derived9177 a h
  have h15 : Entails.eval a c9246 := derived9246 a h
  have h16 : Entails.eval a c9256 := derived9256 a h
  have h17 : Entails.eval a c2892 := h 2891 (by decide)
  have h18 : Entails.eval a c2858 := h 2857 (by decide)
  have h19 : Entails.eval a c2875 := h 2874 (by decide)
  have h20 : Entails.eval a c3053 := h 3052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9258 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨39, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨50, by decide⟩, false), (⟨61, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9229, some c2892, some c2858, some c2875, some c3053, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p9258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9258 : lratChecker f9258 p9258 = .success := by decide +kernel
theorem unsat9258 : Unsatisfiable (PosFin 65) f9258 := by
  apply lratCheckerSound f9258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9258
  · intro a ha; simp [p9258] at ha; subst a; trivial
  · exact checked9258
theorem derived9258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9258 := by
  apply localUnsat_implies_entails f9258 [c9228, c9229, c2892, c2858, c2875, c3053] c9258 unsat9258 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c2892 := h 2891 (by decide)
  have h3 : Entails.eval a c2858 := h 2857 (by decide)
  have h4 : Entails.eval a c2875 := h 2874 (by decide)
  have h5 : Entails.eval a c3053 := h 3052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9259 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨45, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2932, some c3005, some c2960, some c3320, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9259 : lratChecker f9259 p9259 = .success := by decide +kernel
theorem unsat9259 : Unsatisfiable (PosFin 65) f9259 := by
  apply lratCheckerSound f9259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9259
  · intro a ha; simp [p9259] at ha; subst a; trivial
  · exact checked9259
theorem derived9259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9259 := by
  apply localUnsat_implies_entails f9259 [c2932, c3005, c2960, c3320] c9259 unsat9259 (by rfl) a
  have h0 : Entails.eval a c2932 := h 2931 (by decide)
  have h1 : Entails.eval a c3005 := h 3004 (by decide)
  have h2 : Entails.eval a c2960 := h 2959 (by decide)
  have h3 : Entails.eval a c3320 := h 3319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9260 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9233, some c9240, some c9241, some c9255, some c5120, some c5112, some c5117, some c5114, some c5118, some c5124, some c5132, some c5115, some c9257, some c6964, some c9243, some c4632, some c3744, some c7023, some c4190, some c4287, some c5869, some c4453, some c9258, some c9259, some c2840, some c2693, some c3410, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked9260 : lratChecker f9260 p9260 = .success := by decide +kernel
theorem unsat9260 : Unsatisfiable (PosFin 65) f9260 := by
  apply lratCheckerSound f9260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9260
  · intro a ha; simp [p9260] at ha; subst a; trivial
  · exact checked9260
theorem derived9260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9260 := by
  apply localUnsat_implies_entails f9260 [c9229, c9233, c9240, c9241, c9255, c5120, c5112, c5117, c5114, c5118, c5124, c5132, c5115, c9257, c6964, c9243, c4632, c3744, c7023, c4190, c4287, c5869, c4453, c9258, c9259, c2840, c2693, c3410] c9260 unsat9260 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9233 := derived9233 a h
  have h2 : Entails.eval a c9240 := derived9240 a h
  have h3 : Entails.eval a c9241 := derived9241 a h
  have h4 : Entails.eval a c9255 := derived9255 a h
  have h5 : Entails.eval a c5120 := h 5119 (by decide)
  have h6 : Entails.eval a c5112 := h 5111 (by decide)
  have h7 : Entails.eval a c5117 := h 5116 (by decide)
  have h8 : Entails.eval a c5114 := h 5113 (by decide)
  have h9 : Entails.eval a c5118 := h 5117 (by decide)
  have h10 : Entails.eval a c5124 := h 5123 (by decide)
  have h11 : Entails.eval a c5132 := h 5131 (by decide)
  have h12 : Entails.eval a c5115 := h 5114 (by decide)
  have h13 : Entails.eval a c9257 := derived9257 a h
  have h14 : Entails.eval a c6964 := derived6964 a h
  have h15 : Entails.eval a c9243 := derived9243 a h
  have h16 : Entails.eval a c4632 := h 4631 (by decide)
  have h17 : Entails.eval a c3744 := h 3743 (by decide)
  have h18 : Entails.eval a c7023 := derived7023 a h
  have h19 : Entails.eval a c4190 := h 4189 (by decide)
  have h20 : Entails.eval a c4287 := h 4286 (by decide)
  have h21 : Entails.eval a c5869 := h 5868 (by decide)
  have h22 : Entails.eval a c4453 := h 4452 (by decide)
  have h23 : Entails.eval a c9258 := derived9258 a h
  have h24 : Entails.eval a c9259 := derived9259 a h
  have h25 : Entails.eval a c2840 := h 2839 (by decide)
  have h26 : Entails.eval a c2693 := h 2692 (by decide)
  have h27 : Entails.eval a c3410 := h 3409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9261 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨45, by decide⟩, false), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c6969, some c6975, some c6977, some c4998, some c5001, some c5237, some c5147, some c4184, some c3975, some c4959, some c3802, some c4714, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9261 : lratChecker f9261 p9261 = .success := by decide +kernel
theorem unsat9261 : Unsatisfiable (PosFin 65) f9261 := by
  apply lratCheckerSound f9261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9261
  · intro a ha; simp [p9261] at ha; subst a; trivial
  · exact checked9261
theorem derived9261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9261 := by
  apply localUnsat_implies_entails f9261 [c9229, c6969, c6975, c6977, c4998, c5001, c5237, c5147, c4184, c3975, c4959, c3802, c4714] c9261 unsat9261 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c6969 := derived6969 a h
  have h2 : Entails.eval a c6975 := derived6975 a h
  have h3 : Entails.eval a c6977 := derived6977 a h
  have h4 : Entails.eval a c4998 := h 4997 (by decide)
  have h5 : Entails.eval a c5001 := h 5000 (by decide)
  have h6 : Entails.eval a c5237 := h 5236 (by decide)
  have h7 : Entails.eval a c5147 := h 5146 (by decide)
  have h8 : Entails.eval a c4184 := h 4183 (by decide)
  have h9 : Entails.eval a c3975 := h 3974 (by decide)
  have h10 : Entails.eval a c4959 := h 4958 (by decide)
  have h11 : Entails.eval a c3802 := h 3801 (by decide)
  have h12 : Entails.eval a c4714 := h 4713 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9262 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9260, some c6905, some c6969, some c6807, some c7023, some c6813, some c6882, some c9261, some c6894, some c4536, some c5597, some c6897, some c6993, some c5237, some c5605, some c4184, some c3975, some c6923, some c4704, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9262 : lratChecker f9262 p9262 = .success := by decide +kernel
theorem unsat9262 : Unsatisfiable (PosFin 65) f9262 := by
  apply lratCheckerSound f9262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9262
  · intro a ha; simp [p9262] at ha; subst a; trivial
  · exact checked9262
theorem derived9262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9262 := by
  apply localUnsat_implies_entails f9262 [c9229, c9260, c6905, c6969, c6807, c7023, c6813, c6882, c9261, c6894, c4536, c5597, c6897, c6993, c5237, c5605, c4184, c3975, c6923, c4704] c9262 unsat9262 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9260 := derived9260 a h
  have h2 : Entails.eval a c6905 := derived6905 a h
  have h3 : Entails.eval a c6969 := derived6969 a h
  have h4 : Entails.eval a c6807 := derived6807 a h
  have h5 : Entails.eval a c7023 := derived7023 a h
  have h6 : Entails.eval a c6813 := derived6813 a h
  have h7 : Entails.eval a c6882 := derived6882 a h
  have h8 : Entails.eval a c9261 := derived9261 a h
  have h9 : Entails.eval a c6894 := derived6894 a h
  have h10 : Entails.eval a c4536 := h 4535 (by decide)
  have h11 : Entails.eval a c5597 := h 5596 (by decide)
  have h12 : Entails.eval a c6897 := derived6897 a h
  have h13 : Entails.eval a c6993 := derived6993 a h
  have h14 : Entails.eval a c5237 := h 5236 (by decide)
  have h15 : Entails.eval a c5605 := h 5604 (by decide)
  have h16 : Entails.eval a c4184 := h 4183 (by decide)
  have h17 : Entails.eval a c3975 := h 3974 (by decide)
  have h18 : Entails.eval a c6923 := derived6923 a h
  have h19 : Entails.eval a c4704 := h 4703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9263 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6882, some c6893, some c6845, some c4515, some c5587, some c4188, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9263 : lratChecker f9263 p9263 = .success := by decide +kernel
theorem unsat9263 : Unsatisfiable (PosFin 65) f9263 := by
  apply lratCheckerSound f9263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9263
  · intro a ha; simp [p9263] at ha; subst a; trivial
  · exact checked9263
theorem derived9263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9263 := by
  apply localUnsat_implies_entails f9263 [c6882, c6893, c6845, c4515, c5587, c4188] c9263 unsat9263 (by rfl) a
  have h0 : Entails.eval a c6882 := derived6882 a h
  have h1 : Entails.eval a c6893 := derived6893 a h
  have h2 : Entails.eval a c6845 := derived6845 a h
  have h3 : Entails.eval a c4515 := h 4514 (by decide)
  have h4 : Entails.eval a c5587 := h 5586 (by decide)
  have h5 : Entails.eval a c4188 := h 4187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9264 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9262, some c9260, some c9263, some c6865, some c6854, some c6857, some c6813, some c6948, some c6802, some c5957, some c4784, some c6934, some c4781, some c5569, some c4184, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9264 : lratChecker f9264 p9264 = .success := by decide +kernel
theorem unsat9264 : Unsatisfiable (PosFin 65) f9264 := by
  apply lratCheckerSound f9264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9264
  · intro a ha; simp [p9264] at ha; subst a; trivial
  · exact checked9264
theorem derived9264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9264 := by
  apply localUnsat_implies_entails f9264 [c9229, c9262, c9260, c9263, c6865, c6854, c6857, c6813, c6948, c6802, c5957, c4784, c6934, c4781, c5569, c4184] c9264 unsat9264 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9262 := derived9262 a h
  have h2 : Entails.eval a c9260 := derived9260 a h
  have h3 : Entails.eval a c9263 := derived9263 a h
  have h4 : Entails.eval a c6865 := derived6865 a h
  have h5 : Entails.eval a c6854 := derived6854 a h
  have h6 : Entails.eval a c6857 := derived6857 a h
  have h7 : Entails.eval a c6813 := derived6813 a h
  have h8 : Entails.eval a c6948 := derived6948 a h
  have h9 : Entails.eval a c6802 := derived6802 a h
  have h10 : Entails.eval a c5957 := derived5957 a h
  have h11 : Entails.eval a c4784 := h 4783 (by decide)
  have h12 : Entails.eval a c6934 := derived6934 a h
  have h13 : Entails.eval a c4781 := h 4780 (by decide)
  have h14 : Entails.eval a c5569 := h 5568 (by decide)
  have h15 : Entails.eval a c4184 := h 4183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9265 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9262, some c9260, some c9264, some c6891, some c6932, some c6947, some c6865, some c6856, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9265 : lratChecker f9265 p9265 = .success := by decide +kernel
theorem unsat9265 : Unsatisfiable (PosFin 65) f9265 := by
  apply lratCheckerSound f9265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9265
  · intro a ha; simp [p9265] at ha; subst a; trivial
  · exact checked9265
theorem derived9265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9265 := by
  apply localUnsat_implies_entails f9265 [c9262, c9260, c9264, c6891, c6932, c6947, c6865, c6856] c9265 unsat9265 (by rfl) a
  have h0 : Entails.eval a c9262 := derived9262 a h
  have h1 : Entails.eval a c9260 := derived9260 a h
  have h2 : Entails.eval a c9264 := derived9264 a h
  have h3 : Entails.eval a c6891 := derived6891 a h
  have h4 : Entails.eval a c6932 := derived6932 a h
  have h5 : Entails.eval a c6947 := derived6947 a h
  have h6 : Entails.eval a c6865 := derived6865 a h
  have h7 : Entails.eval a c6856 := derived6856 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9266 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨63, by decide⟩, true), (⟨48, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨57, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4098, some c4984, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9266 : lratChecker f9266 p9266 = .success := by decide +kernel
theorem unsat9266 : Unsatisfiable (PosFin 65) f9266 := by
  apply lratCheckerSound f9266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9266
  · intro a ha; simp [p9266] at ha; subst a; trivial
  · exact checked9266
theorem derived9266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9266 := by
  apply localUnsat_implies_entails f9266 [c4098, c4984] c9266 unsat9266 (by rfl) a
  have h0 : Entails.eval a c4098 := h 4097 (by decide)
  have h1 : Entails.eval a c4984 := h 4983 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9267 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7000, some c6879, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p9267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9267 : lratChecker f9267 p9267 = .success := by decide +kernel
theorem unsat9267 : Unsatisfiable (PosFin 65) f9267 := by
  apply lratCheckerSound f9267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9267
  · intro a ha; simp [p9267] at ha; subst a; trivial
  · exact checked9267
theorem derived9267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9267 := by
  apply localUnsat_implies_entails f9267 [c7000, c6879] c9267 unsat9267 (by rfl) a
  have h0 : Entails.eval a c7000 := derived7000 a h
  have h1 : Entails.eval a c6879 := derived6879 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9268 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3368, some c3405, some c2765, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9268 : lratChecker f9268 p9268 = .success := by decide +kernel
theorem unsat9268 : Unsatisfiable (PosFin 65) f9268 := by
  apply lratCheckerSound f9268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9268
  · intro a ha; simp [p9268] at ha; subst a; trivial
  · exact checked9268
theorem derived9268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9268 := by
  apply localUnsat_implies_entails f9268 [c3368, c3405, c2765] c9268 unsat9268 (by rfl) a
  have h0 : Entails.eval a c3368 := h 3367 (by decide)
  have h1 : Entails.eval a c3405 := h 3404 (by decide)
  have h2 : Entails.eval a c2765 := h 2764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9269 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨61, by decide⟩, true), (⟨55, by decide⟩, false), (⟨38, by decide⟩, true), (⟨51, by decide⟩, true), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c2986, some c2917, some c2998, some c3175, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9269 : lratChecker f9269 p9269 = .success := by decide +kernel
theorem unsat9269 : Unsatisfiable (PosFin 65) f9269 := by
  apply lratCheckerSound f9269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9269
  · intro a ha; simp [p9269] at ha; subst a; trivial
  · exact checked9269
theorem derived9269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9269 := by
  apply localUnsat_implies_entails f9269 [c9228, c2986, c2917, c2998, c3175] c9269 unsat9269 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c2986 := h 2985 (by decide)
  have h2 : Entails.eval a c2917 := h 2916 (by decide)
  have h3 : Entails.eval a c2998 := h 2997 (by decide)
  have h4 : Entails.eval a c3175 := h 3174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9270 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨61, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, true), (⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, false), (⟨40, by decide⟩, false), (⟨41, by decide⟩, true), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c6969, some c7016, some c6845, some c9266, some c7004, some c9065, some c7038, some c9268, some c9269, some c2931, some c3007, some c2955, some c3319, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9270 : lratChecker f9270 p9270 = .success := by decide +kernel
theorem unsat9270 : Unsatisfiable (PosFin 65) f9270 := by
  apply lratCheckerSound f9270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9270
  · intro a ha; simp [p9270] at ha; subst a; trivial
  · exact checked9270
theorem derived9270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9270 := by
  apply localUnsat_implies_entails f9270 [c9229, c6969, c7016, c6845, c9266, c7004, c9065, c7038, c9268, c9269, c2931, c3007, c2955, c3319] c9270 unsat9270 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c6969 := derived6969 a h
  have h2 : Entails.eval a c7016 := derived7016 a h
  have h3 : Entails.eval a c6845 := derived6845 a h
  have h4 : Entails.eval a c9266 := derived9266 a h
  have h5 : Entails.eval a c7004 := derived7004 a h
  have h6 : Entails.eval a c9065 := derived9065 a h
  have h7 : Entails.eval a c7038 := derived7038 a h
  have h8 : Entails.eval a c9268 := derived9268 a h
  have h9 : Entails.eval a c9269 := derived9269 a h
  have h10 : Entails.eval a c2931 := h 2930 (by decide)
  have h11 : Entails.eval a c3007 := h 3006 (by decide)
  have h12 : Entails.eval a c2955 := h 2954 (by decide)
  have h13 : Entails.eval a c3319 := h 3318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9271 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨59, by decide⟩, true), (⟨38, by decide⟩, true), (⟨63, by decide⟩, false), (⟨48, by decide⟩, true), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2885, some c2740, some c2924, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9271 : lratChecker f9271 p9271 = .success := by decide +kernel
theorem unsat9271 : Unsatisfiable (PosFin 65) f9271 := by
  apply lratCheckerSound f9271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9271
  · intro a ha; simp [p9271] at ha; subst a; trivial
  · exact checked9271
theorem derived9271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9271 := by
  apply localUnsat_implies_entails f9271 [c2885, c2740, c2924] c9271 unsat9271 (by rfl) a
  have h0 : Entails.eval a c2885 := h 2884 (by decide)
  have h1 : Entails.eval a c2740 := h 2739 (by decide)
  have h2 : Entails.eval a c2924 := h 2923 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9272 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, true), (⟨63, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨46, by decide⟩, false), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5938, some c9271, some c2952, some c6729, some c2785, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9272 : lratChecker f9272 p9272 = .success := by decide +kernel
theorem unsat9272 : Unsatisfiable (PosFin 65) f9272 := by
  apply lratCheckerSound f9272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9272
  · intro a ha; simp [p9272] at ha; subst a; trivial
  · exact checked9272
theorem derived9272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9272 := by
  apply localUnsat_implies_entails f9272 [c5938, c9271, c2952, c6729, c2785] c9272 unsat9272 (by rfl) a
  have h0 : Entails.eval a c5938 := derived5938 a h
  have h1 : Entails.eval a c9271 := derived9271 a h
  have h2 : Entails.eval a c2952 := h 2951 (by decide)
  have h3 : Entails.eval a c6729 := derived6729 a h
  have h4 : Entails.eval a c2785 := h 2784 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9273 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, false), (⟨51, by decide⟩, true), (⟨62, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3217, some c6770, some c3260, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9273 : lratChecker f9273 p9273 = .success := by decide +kernel
theorem unsat9273 : Unsatisfiable (PosFin 65) f9273 := by
  apply lratCheckerSound f9273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9273
  · intro a ha; simp [p9273] at ha; subst a; trivial
  · exact checked9273
theorem derived9273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9273 := by
  apply localUnsat_implies_entails f9273 [c3217, c6770, c3260] c9273 unsat9273 (by rfl) a
  have h0 : Entails.eval a c3217 := h 3216 (by decide)
  have h1 : Entails.eval a c6770 := derived6770 a h
  have h2 : Entails.eval a c3260 := h 3259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9274 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9230, some c9265, some c9262, some c9260, some c6969, some c7016, some c6845, some c7038, some c6891, some c9267, some c9068, some c9266, some c6857, some c6948, some c4099, some c6921, some c7004, some c4424, some c5938, some c3958, some c9065, some c9270, some c9272, some c9269, some c9273, some c1, some c2885, some c2765, some c2740, some c646, some c96, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked9274 : lratChecker f9274 p9274 = .success := by decide +kernel
theorem unsat9274 : Unsatisfiable (PosFin 65) f9274 := by
  apply lratCheckerSound f9274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9274
  · intro a ha; simp [p9274] at ha; subst a; trivial
  · exact checked9274
theorem derived9274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9274 := by
  apply localUnsat_implies_entails f9274 [c9229, c9228, c9230, c9265, c9262, c9260, c6969, c7016, c6845, c7038, c6891, c9267, c9068, c9266, c6857, c6948, c4099, c6921, c7004, c4424, c5938, c3958, c9065, c9270, c9272, c9269, c9273, c1, c2885, c2765, c2740, c646, c96] c9274 unsat9274 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9230 := derived9230 a h
  have h3 : Entails.eval a c9265 := derived9265 a h
  have h4 : Entails.eval a c9262 := derived9262 a h
  have h5 : Entails.eval a c9260 := derived9260 a h
  have h6 : Entails.eval a c6969 := derived6969 a h
  have h7 : Entails.eval a c7016 := derived7016 a h
  have h8 : Entails.eval a c6845 := derived6845 a h
  have h9 : Entails.eval a c7038 := derived7038 a h
  have h10 : Entails.eval a c6891 := derived6891 a h
  have h11 : Entails.eval a c9267 := derived9267 a h
  have h12 : Entails.eval a c9068 := derived9068 a h
  have h13 : Entails.eval a c9266 := derived9266 a h
  have h14 : Entails.eval a c6857 := derived6857 a h
  have h15 : Entails.eval a c6948 := derived6948 a h
  have h16 : Entails.eval a c4099 := h 4098 (by decide)
  have h17 : Entails.eval a c6921 := derived6921 a h
  have h18 : Entails.eval a c7004 := derived7004 a h
  have h19 : Entails.eval a c4424 := h 4423 (by decide)
  have h20 : Entails.eval a c5938 := derived5938 a h
  have h21 : Entails.eval a c3958 := h 3957 (by decide)
  have h22 : Entails.eval a c9065 := derived9065 a h
  have h23 : Entails.eval a c9270 := derived9270 a h
  have h24 : Entails.eval a c9272 := derived9272 a h
  have h25 : Entails.eval a c9269 := derived9269 a h
  have h26 : Entails.eval a c9273 := derived9273 a h
  have h27 : Entails.eval a c1 := h 0 (by decide)
  have h28 : Entails.eval a c2885 := h 2884 (by decide)
  have h29 : Entails.eval a c2765 := h 2764 (by decide)
  have h30 : Entails.eval a c2740 := h 2739 (by decide)
  have h31 : Entails.eval a c646 := h 645 (by decide)
  have h32 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9275 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨61, by decide⟩, true), (⟨50, by decide⟩, true), (⟨59, by decide⟩, true), (⟨51, by decide⟩, true), (⟨62, by decide⟩, false), (⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9230, some c1, some c2771, some c2765, some c2740, some c647, some c96, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9275 : lratChecker f9275 p9275 = .success := by decide +kernel
theorem unsat9275 : Unsatisfiable (PosFin 65) f9275 := by
  apply lratCheckerSound f9275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9275
  · intro a ha; simp [p9275] at ha; subst a; trivial
  · exact checked9275
theorem derived9275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9275 := by
  apply localUnsat_implies_entails f9275 [c9230, c1, c2771, c2765, c2740, c647, c96] c9275 unsat9275 (by rfl) a
  have h0 : Entails.eval a c9230 := derived9230 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c2771 := h 2770 (by decide)
  have h3 : Entails.eval a c2765 := h 2764 (by decide)
  have h4 : Entails.eval a c2740 := h 2739 (by decide)
  have h5 : Entails.eval a c647 := h 646 (by decide)
  have h6 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9276 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨50, by decide⟩, true), (⟨63, by decide⟩, false), (⟨51, by decide⟩, true), (⟨62, by decide⟩, false), (⟨49, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6768, some c9273, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9276 : lratChecker f9276 p9276 = .success := by decide +kernel
theorem unsat9276 : Unsatisfiable (PosFin 65) f9276 := by
  apply lratCheckerSound f9276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9276
  · intro a ha; simp [p9276] at ha; subst a; trivial
  · exact checked9276
theorem derived9276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9276 := by
  apply localUnsat_implies_entails f9276 [c6768, c9273] c9276 unsat9276 (by rfl) a
  have h0 : Entails.eval a c6768 := derived6768 a h
  have h1 : Entails.eval a c9273 := derived9273 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9277 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨38, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6725, some c6752, some c2920, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9277 : lratChecker f9277 p9277 = .success := by decide +kernel
theorem unsat9277 : Unsatisfiable (PosFin 65) f9277 := by
  apply lratCheckerSound f9277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9277
  · intro a ha; simp [p9277] at ha; subst a; trivial
  · exact checked9277
theorem derived9277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9277 := by
  apply localUnsat_implies_entails f9277 [c6725, c6752, c2920] c9277 unsat9277 (by rfl) a
  have h0 : Entails.eval a c6725 := derived6725 a h
  have h1 : Entails.eval a c6752 := derived6752 a h
  have h2 : Entails.eval a c2920 := h 2919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9278 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨61, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨57, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3415, some c2811, some c6721, some c3423, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9278 : lratChecker f9278 p9278 = .success := by decide +kernel
theorem unsat9278 : Unsatisfiable (PosFin 65) f9278 := by
  apply lratCheckerSound f9278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9278
  · intro a ha; simp [p9278] at ha; subst a; trivial
  · exact checked9278
theorem derived9278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9278 := by
  apply localUnsat_implies_entails f9278 [c3415, c2811, c6721, c3423] c9278 unsat9278 (by rfl) a
  have h0 : Entails.eval a c3415 := h 3414 (by decide)
  have h1 : Entails.eval a c2811 := h 2810 (by decide)
  have h2 : Entails.eval a c6721 := derived6721 a h
  have h3 : Entails.eval a c3423 := h 3422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9279 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9228, some c9260, some c9265, some c6969, some c7038, some c6891, some c9267, some c9068, some c9262, some c7016, some c6845, some c6857, some c9266, some c9274, some c7008, some c6999, some c5276, some c9065, some c5291, some c9275, some c9276, some c9278, some c9277, some c3294, some c3289, some c3307, some c3388, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked9279 : lratChecker f9279 p9279 = .success := by decide +kernel
theorem unsat9279 : Unsatisfiable (PosFin 65) f9279 := by
  apply lratCheckerSound f9279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9279
  · intro a ha; simp [p9279] at ha; subst a; trivial
  · exact checked9279
theorem derived9279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9279 := by
  apply localUnsat_implies_entails f9279 [c9229, c9228, c9260, c9265, c6969, c7038, c6891, c9267, c9068, c9262, c7016, c6845, c6857, c9266, c9274, c7008, c6999, c5276, c9065, c5291, c9275, c9276, c9278, c9277, c3294, c3289, c3307, c3388] c9279 unsat9279 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c9260 := derived9260 a h
  have h3 : Entails.eval a c9265 := derived9265 a h
  have h4 : Entails.eval a c6969 := derived6969 a h
  have h5 : Entails.eval a c7038 := derived7038 a h
  have h6 : Entails.eval a c6891 := derived6891 a h
  have h7 : Entails.eval a c9267 := derived9267 a h
  have h8 : Entails.eval a c9068 := derived9068 a h
  have h9 : Entails.eval a c9262 := derived9262 a h
  have h10 : Entails.eval a c7016 := derived7016 a h
  have h11 : Entails.eval a c6845 := derived6845 a h
  have h12 : Entails.eval a c6857 := derived6857 a h
  have h13 : Entails.eval a c9266 := derived9266 a h
  have h14 : Entails.eval a c9274 := derived9274 a h
  have h15 : Entails.eval a c7008 := derived7008 a h
  have h16 : Entails.eval a c6999 := derived6999 a h
  have h17 : Entails.eval a c5276 := h 5275 (by decide)
  have h18 : Entails.eval a c9065 := derived9065 a h
  have h19 : Entails.eval a c5291 := h 5290 (by decide)
  have h20 : Entails.eval a c9275 := derived9275 a h
  have h21 : Entails.eval a c9276 := derived9276 a h
  have h22 : Entails.eval a c9278 := derived9278 a h
  have h23 : Entails.eval a c9277 := derived9277 a h
  have h24 : Entails.eval a c3294 := h 3293 (by decide)
  have h25 : Entails.eval a c3289 := h 3288 (by decide)
  have h26 : Entails.eval a c3307 := h 3306 (by decide)
  have h27 : Entails.eval a c3388 := h 3387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9280 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨57, by decide⟩, true), (⟨35, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9260, some c9265, some c6969, some c7016, some c7038, some c6891, some c9267, some c9068, some c9279, some c5031, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p9280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9280 : lratChecker f9280 p9280 = .success := by decide +kernel
theorem unsat9280 : Unsatisfiable (PosFin 65) f9280 := by
  apply lratCheckerSound f9280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9280
  · intro a ha; simp [p9280] at ha; subst a; trivial
  · exact checked9280
theorem derived9280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9280 := by
  apply localUnsat_implies_entails f9280 [c9229, c9260, c9265, c6969, c7016, c7038, c6891, c9267, c9068, c9279, c5031] c9280 unsat9280 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9260 := derived9260 a h
  have h2 : Entails.eval a c9265 := derived9265 a h
  have h3 : Entails.eval a c6969 := derived6969 a h
  have h4 : Entails.eval a c7016 := derived7016 a h
  have h5 : Entails.eval a c7038 := derived7038 a h
  have h6 : Entails.eval a c6891 := derived6891 a h
  have h7 : Entails.eval a c9267 := derived9267 a h
  have h8 : Entails.eval a c9068 := derived9068 a h
  have h9 : Entails.eval a c9279 := derived9279 a h
  have h10 : Entails.eval a c5031 := h 5030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9280

end CochromaticTwenty.Certificates.FixedCore1
