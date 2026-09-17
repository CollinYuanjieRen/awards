import MerLeanExperiment.Certificates.FixedCore1.Steps0200_0299

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6181 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6181 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4991, some c5311, some c4685, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6181 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6181 : lratChecker f6181 p6181 = .success := by decide +kernel
theorem unsat6181 : Unsatisfiable (PosFin 65) f6181 := by
  apply lratCheckerSound f6181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6181
  · intro a ha; simp [p6181] at ha; subst a; trivial
  · exact checked6181
theorem derived6181 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6181 := by
  apply localUnsat_implies_entails f6181 [c4991, c5311, c4685] c6181 unsat6181 (by rfl) a
  have h0 : Entails.eval a c4991 := h 4990 (by decide)
  have h1 : Entails.eval a c5311 := h 5310 (by decide)
  have h2 : Entails.eval a c4685 := h 4684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6182 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨52, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6182 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6172, some c6180, some c6179, some c6181, some c4435, some c4500, some c4702, some c3817, some c5808, some c4657, some c3475, some c5920, some c6177, some c5008, some c5916, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6182 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6182 : lratChecker f6182 p6182 = .success := by decide +kernel
theorem unsat6182 : Unsatisfiable (PosFin 65) f6182 := by
  apply lratCheckerSound f6182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6182
  · intro a ha; simp [p6182] at ha; subst a; trivial
  · exact checked6182
theorem derived6182 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6182 := by
  apply localUnsat_implies_entails f6182 [c6172, c6180, c6179, c6181, c4435, c4500, c4702, c3817, c5808, c4657, c3475, c5920, c6177, c5008, c5916] c6182 unsat6182 (by rfl) a
  have h0 : Entails.eval a c6172 := derived6172 a h
  have h1 : Entails.eval a c6180 := derived6180 a h
  have h2 : Entails.eval a c6179 := derived6179 a h
  have h3 : Entails.eval a c6181 := derived6181 a h
  have h4 : Entails.eval a c4435 := h 4434 (by decide)
  have h5 : Entails.eval a c4500 := h 4499 (by decide)
  have h6 : Entails.eval a c4702 := h 4701 (by decide)
  have h7 : Entails.eval a c3817 := h 3816 (by decide)
  have h8 : Entails.eval a c5808 := h 5807 (by decide)
  have h9 : Entails.eval a c4657 := h 4656 (by decide)
  have h10 : Entails.eval a c3475 := h 3474 (by decide)
  have h11 : Entails.eval a c5920 := derived5920 a h
  have h12 : Entails.eval a c6177 := derived6177 a h
  have h13 : Entails.eval a c5008 := h 5007 (by decide)
  have h14 : Entails.eval a c5916 := derived5916 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6183 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, true), (⟨48, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6183 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6178, some c6095, some c6180, some c6179, some c6181, some c4702, some c3817, some c4657, some c6172, some c4435, some c6038, some c4500, some c6182, some c6104, some c5128, some c4870, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6183 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6183 : lratChecker f6183 p6183 = .success := by decide +kernel
theorem unsat6183 : Unsatisfiable (PosFin 65) f6183 := by
  apply lratCheckerSound f6183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6183
  · intro a ha; simp [p6183] at ha; subst a; trivial
  · exact checked6183
theorem derived6183 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6183 := by
  apply localUnsat_implies_entails f6183 [c6139, c6178, c6095, c6180, c6179, c6181, c4702, c3817, c4657, c6172, c4435, c6038, c4500, c6182, c6104, c5128, c4870] c6183 unsat6183 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6178 := derived6178 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6180 := derived6180 a h
  have h4 : Entails.eval a c6179 := derived6179 a h
  have h5 : Entails.eval a c6181 := derived6181 a h
  have h6 : Entails.eval a c4702 := h 4701 (by decide)
  have h7 : Entails.eval a c3817 := h 3816 (by decide)
  have h8 : Entails.eval a c4657 := h 4656 (by decide)
  have h9 : Entails.eval a c6172 := derived6172 a h
  have h10 : Entails.eval a c4435 := h 4434 (by decide)
  have h11 : Entails.eval a c6038 := derived6038 a h
  have h12 : Entails.eval a c4500 := h 4499 (by decide)
  have h13 : Entails.eval a c6182 := derived6182 a h
  have h14 : Entails.eval a c6104 := derived6104 a h
  have h15 : Entails.eval a c5128 := h 5127 (by decide)
  have h16 : Entails.eval a c4870 := h 4869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6184 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨41, by decide⟩, false), (⟨38, by decide⟩, true), (⟨45, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6184 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5415, some c5126, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6184 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6184 : lratChecker f6184 p6184 = .success := by decide +kernel
theorem unsat6184 : Unsatisfiable (PosFin 65) f6184 := by
  apply lratCheckerSound f6184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6184
  · intro a ha; simp [p6184] at ha; subst a; trivial
  · exact checked6184
theorem derived6184 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6184 := by
  apply localUnsat_implies_entails f6184 [c5415, c5126] c6184 unsat6184 (by rfl) a
  have h0 : Entails.eval a c5415 := h 5414 (by decide)
  have h1 : Entails.eval a c5126 := h 5125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6185 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨61, by decide⟩, true), (⟨47, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨48, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6185 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2721, some c2748, some c2824, some c3142, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6185 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6185 : lratChecker f6185 p6185 = .success := by decide +kernel
theorem unsat6185 : Unsatisfiable (PosFin 65) f6185 := by
  apply lratCheckerSound f6185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6185
  · intro a ha; simp [p6185] at ha; subst a; trivial
  · exact checked6185
theorem derived6185 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6185 := by
  apply localUnsat_implies_entails f6185 [c2721, c2748, c2824, c3142] c6185 unsat6185 (by rfl) a
  have h0 : Entails.eval a c2721 := h 2720 (by decide)
  have h1 : Entails.eval a c2748 := h 2747 (by decide)
  have h2 : Entails.eval a c2824 := h 2823 (by decide)
  have h3 : Entails.eval a c3142 := h 3141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6186 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨58, by decide⟩, true), (⟨57, by decide⟩, false), (⟨56, by decide⟩, false), (⟨49, by decide⟩, false), (⟨61, by decide⟩, true), (⟨37, by decide⟩, false), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6186 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3128, some c3419, some c3020, some c2908, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6186 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6186 : lratChecker f6186 p6186 = .success := by decide +kernel
theorem unsat6186 : Unsatisfiable (PosFin 65) f6186 := by
  apply lratCheckerSound f6186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6186
  · intro a ha; simp [p6186] at ha; subst a; trivial
  · exact checked6186
theorem derived6186 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6186 := by
  apply localUnsat_implies_entails f6186 [c3128, c3419, c3020, c2908] c6186 unsat6186 (by rfl) a
  have h0 : Entails.eval a c3128 := h 3127 (by decide)
  have h1 : Entails.eval a c3419 := h 3418 (by decide)
  have h2 : Entails.eval a c3020 := h 3019 (by decide)
  have h3 : Entails.eval a c2908 := h 2907 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6187 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨57, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨60, by decide⟩, false), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6187 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2831, some c2837, some c2847, some c3176, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p6187 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6187 : lratChecker f6187 p6187 = .success := by decide +kernel
theorem unsat6187 : Unsatisfiable (PosFin 65) f6187 := by
  apply lratCheckerSound f6187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6187
  · intro a ha; simp [p6187] at ha; subst a; trivial
  · exact checked6187
theorem derived6187 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6187 := by
  apply localUnsat_implies_entails f6187 [c2831, c2837, c2847, c3176] c6187 unsat6187 (by rfl) a
  have h0 : Entails.eval a c2831 := h 2830 (by decide)
  have h1 : Entails.eval a c2837 := h 2836 (by decide)
  have h2 : Entails.eval a c2847 := h 2846 (by decide)
  have h3 : Entails.eval a c3176 := h 3175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6188 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6188 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6178, some c6095, some c6172, some c6180, some c6179, some c6181, some c4702, some c3817, some c4657, some c6184, some c6183, some c6182, some c6038, some c5808, some c4435, some c5061, some c5050, some c5072, some c3875, some c4480, some c4604, some c5677, some c3866, some c6185, some c6186, some c6187, some c2941, some c2972, some c3325, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6188 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6188 : lratChecker f6188 p6188 = .success := by decide +kernel
theorem unsat6188 : Unsatisfiable (PosFin 65) f6188 := by
  apply lratCheckerSound f6188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6188
  · intro a ha; simp [p6188] at ha; subst a; trivial
  · exact checked6188
theorem derived6188 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6188 := by
  apply localUnsat_implies_entails f6188 [c6139, c6178, c6095, c6172, c6180, c6179, c6181, c4702, c3817, c4657, c6184, c6183, c6182, c6038, c5808, c4435, c5061, c5050, c5072, c3875, c4480, c4604, c5677, c3866, c6185, c6186, c6187, c2941, c2972, c3325] c6188 unsat6188 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6178 := derived6178 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6172 := derived6172 a h
  have h4 : Entails.eval a c6180 := derived6180 a h
  have h5 : Entails.eval a c6179 := derived6179 a h
  have h6 : Entails.eval a c6181 := derived6181 a h
  have h7 : Entails.eval a c4702 := h 4701 (by decide)
  have h8 : Entails.eval a c3817 := h 3816 (by decide)
  have h9 : Entails.eval a c4657 := h 4656 (by decide)
  have h10 : Entails.eval a c6184 := derived6184 a h
  have h11 : Entails.eval a c6183 := derived6183 a h
  have h12 : Entails.eval a c6182 := derived6182 a h
  have h13 : Entails.eval a c6038 := derived6038 a h
  have h14 : Entails.eval a c5808 := h 5807 (by decide)
  have h15 : Entails.eval a c4435 := h 4434 (by decide)
  have h16 : Entails.eval a c5061 := h 5060 (by decide)
  have h17 : Entails.eval a c5050 := h 5049 (by decide)
  have h18 : Entails.eval a c5072 := h 5071 (by decide)
  have h19 : Entails.eval a c3875 := h 3874 (by decide)
  have h20 : Entails.eval a c4480 := h 4479 (by decide)
  have h21 : Entails.eval a c4604 := h 4603 (by decide)
  have h22 : Entails.eval a c5677 := h 5676 (by decide)
  have h23 : Entails.eval a c3866 := h 3865 (by decide)
  have h24 : Entails.eval a c6185 := derived6185 a h
  have h25 : Entails.eval a c6186 := derived6186 a h
  have h26 : Entails.eval a c6187 := derived6187 a h
  have h27 : Entails.eval a c2941 := h 2940 (by decide)
  have h28 : Entails.eval a c2972 := h 2971 (by decide)
  have h29 : Entails.eval a c3325 := h 3324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6189 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨60, by decide⟩, false), (⟨47, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6189 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2941, some c2972, some c3325, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6189 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6189 : lratChecker f6189 p6189 = .success := by decide +kernel
theorem unsat6189 : Unsatisfiable (PosFin 65) f6189 := by
  apply lratCheckerSound f6189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6189
  · intro a ha; simp [p6189] at ha; subst a; trivial
  · exact checked6189
theorem derived6189 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6189 := by
  apply localUnsat_implies_entails f6189 [c2941, c2972, c3325] c6189 unsat6189 (by rfl) a
  have h0 : Entails.eval a c2941 := h 2940 (by decide)
  have h1 : Entails.eval a c2972 := h 2971 (by decide)
  have h2 : Entails.eval a c3325 := h 3324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6190 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6190 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6178, some c6095, some c6139, some c6172, some c6180, some c6179, some c6181, some c4702, some c4435, some c3817, some c3475, some c4657, some c5808, some c6184, some c6038, some c4500, some c6182, some c6183, some c6188, some c4073, some c4068, some c4271, some c5786, some c4238, some c4857, some c4076, some c4854, some c6185, some c6186, some c6189, some c2830, some c2836, some c2846, some c3180, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6190 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked6190 : lratChecker f6190 p6190 = .success := by decide +kernel
theorem unsat6190 : Unsatisfiable (PosFin 65) f6190 := by
  apply lratCheckerSound f6190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6190
  · intro a ha; simp [p6190] at ha; subst a; trivial
  · exact checked6190
theorem derived6190 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6190 := by
  apply localUnsat_implies_entails f6190 [c6178, c6095, c6139, c6172, c6180, c6179, c6181, c4702, c4435, c3817, c3475, c4657, c5808, c6184, c6038, c4500, c6182, c6183, c6188, c4073, c4068, c4271, c5786, c4238, c4857, c4076, c4854, c6185, c6186, c6189, c2830, c2836, c2846, c3180] c6190 unsat6190 (by rfl) a
  have h0 : Entails.eval a c6178 := derived6178 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6139 := derived6139 a h
  have h3 : Entails.eval a c6172 := derived6172 a h
  have h4 : Entails.eval a c6180 := derived6180 a h
  have h5 : Entails.eval a c6179 := derived6179 a h
  have h6 : Entails.eval a c6181 := derived6181 a h
  have h7 : Entails.eval a c4702 := h 4701 (by decide)
  have h8 : Entails.eval a c4435 := h 4434 (by decide)
  have h9 : Entails.eval a c3817 := h 3816 (by decide)
  have h10 : Entails.eval a c3475 := h 3474 (by decide)
  have h11 : Entails.eval a c4657 := h 4656 (by decide)
  have h12 : Entails.eval a c5808 := h 5807 (by decide)
  have h13 : Entails.eval a c6184 := derived6184 a h
  have h14 : Entails.eval a c6038 := derived6038 a h
  have h15 : Entails.eval a c4500 := h 4499 (by decide)
  have h16 : Entails.eval a c6182 := derived6182 a h
  have h17 : Entails.eval a c6183 := derived6183 a h
  have h18 : Entails.eval a c6188 := derived6188 a h
  have h19 : Entails.eval a c4073 := h 4072 (by decide)
  have h20 : Entails.eval a c4068 := h 4067 (by decide)
  have h21 : Entails.eval a c4271 := h 4270 (by decide)
  have h22 : Entails.eval a c5786 := h 5785 (by decide)
  have h23 : Entails.eval a c4238 := h 4237 (by decide)
  have h24 : Entails.eval a c4857 := h 4856 (by decide)
  have h25 : Entails.eval a c4076 := h 4075 (by decide)
  have h26 : Entails.eval a c4854 := h 4853 (by decide)
  have h27 : Entails.eval a c6185 := derived6185 a h
  have h28 : Entails.eval a c6186 := derived6186 a h
  have h29 : Entails.eval a c6189 := derived6189 a h
  have h30 : Entails.eval a c2830 := h 2829 (by decide)
  have h31 : Entails.eval a c2836 := h 2835 (by decide)
  have h32 : Entails.eval a c2846 := h 2845 (by decide)
  have h33 : Entails.eval a c3180 := h 3179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6191 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6191 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5355, some c4102, some c3475, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6191 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6191 : lratChecker f6191 p6191 = .success := by decide +kernel
theorem unsat6191 : Unsatisfiable (PosFin 65) f6191 := by
  apply lratCheckerSound f6191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6191
  · intro a ha; simp [p6191] at ha; subst a; trivial
  · exact checked6191
theorem derived6191 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6191 := by
  apply localUnsat_implies_entails f6191 [c5355, c4102, c3475] c6191 unsat6191 (by rfl) a
  have h0 : Entails.eval a c5355 := h 5354 (by decide)
  have h1 : Entails.eval a c4102 := h 4101 (by decide)
  have h2 : Entails.eval a c3475 := h 3474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6192 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6192 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6181, some c4991, some c5311, some c3522, some c4392, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6192 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6192 : lratChecker f6192 p6192 = .success := by decide +kernel
theorem unsat6192 : Unsatisfiable (PosFin 65) f6192 := by
  apply lratCheckerSound f6192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6192
  · intro a ha; simp [p6192] at ha; subst a; trivial
  · exact checked6192
theorem derived6192 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6192 := by
  apply localUnsat_implies_entails f6192 [c6181, c4991, c5311, c3522, c4392] c6192 unsat6192 (by rfl) a
  have h0 : Entails.eval a c6181 := derived6181 a h
  have h1 : Entails.eval a c4991 := h 4990 (by decide)
  have h2 : Entails.eval a c5311 := h 5310 (by decide)
  have h3 : Entails.eval a c3522 := h 3521 (by decide)
  have h4 : Entails.eval a c4392 := h 4391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6193 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨55, by decide⟩, true), (⟨62, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6193 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6191, some c6192, some c6179, some c4201, some c3444, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6193 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6193 : lratChecker f6193 p6193 = .success := by decide +kernel
theorem unsat6193 : Unsatisfiable (PosFin 65) f6193 := by
  apply lratCheckerSound f6193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6193
  · intro a ha; simp [p6193] at ha; subst a; trivial
  · exact checked6193
theorem derived6193 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6193 := by
  apply localUnsat_implies_entails f6193 [c6191, c6192, c6179, c4201, c3444] c6193 unsat6193 (by rfl) a
  have h0 : Entails.eval a c6191 := derived6191 a h
  have h1 : Entails.eval a c6192 := derived6192 a h
  have h2 : Entails.eval a c6179 := derived6179 a h
  have h3 : Entails.eval a c4201 := h 4200 (by decide)
  have h4 : Entails.eval a c3444 := h 3443 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6194 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6194 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6178, some c6095, some c6190, some c6193, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6194 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6194 : lratChecker f6194 p6194 = .success := by decide +kernel
theorem unsat6194 : Unsatisfiable (PosFin 65) f6194 := by
  apply lratCheckerSound f6194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6194
  · intro a ha; simp [p6194] at ha; subst a; trivial
  · exact checked6194
theorem derived6194 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6194 := by
  apply localUnsat_implies_entails f6194 [c6139, c6178, c6095, c6190, c6193] c6194 unsat6194 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6178 := derived6178 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6190 := derived6190 a h
  have h4 : Entails.eval a c6193 := derived6193 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6195 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6195 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6139, some c6114, some c6109, some c4037, some c4173, some c5904, some c4996, some c4103, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6195 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6195 : lratChecker f6195 p6195 = .success := by decide +kernel
theorem unsat6195 : Unsatisfiable (PosFin 65) f6195 := by
  apply lratCheckerSound f6195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6195
  · intro a ha; simp [p6195] at ha; subst a; trivial
  · exact checked6195
theorem derived6195 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6195 := by
  apply localUnsat_implies_entails f6195 [c6194, c6139, c6114, c6109, c4037, c4173, c5904, c4996, c4103] c6195 unsat6195 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6139 := derived6139 a h
  have h2 : Entails.eval a c6114 := derived6114 a h
  have h3 : Entails.eval a c6109 := derived6109 a h
  have h4 : Entails.eval a c4037 := h 4036 (by decide)
  have h5 : Entails.eval a c4173 := h 4172 (by decide)
  have h6 : Entails.eval a c5904 := derived5904 a h
  have h7 : Entails.eval a c4996 := h 4995 (by decide)
  have h8 : Entails.eval a c4103 := h 4102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6196 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6196 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6118, some c5724, some c5339, some c3655, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6196 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6196 : lratChecker f6196 p6196 = .success := by decide +kernel
theorem unsat6196 : Unsatisfiable (PosFin 65) f6196 := by
  apply lratCheckerSound f6196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6196
  · intro a ha; simp [p6196] at ha; subst a; trivial
  · exact checked6196
theorem derived6196 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6196 := by
  apply localUnsat_implies_entails f6196 [c6118, c5724, c5339, c3655] c6196 unsat6196 (by rfl) a
  have h0 : Entails.eval a c6118 := derived6118 a h
  have h1 : Entails.eval a c5724 := h 5723 (by decide)
  have h2 : Entails.eval a c5339 := h 5338 (by decide)
  have h3 : Entails.eval a c3655 := h 3654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6197 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6197 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6139, some c6195, some c6196, some c3793, some c3796, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6197 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6197 : lratChecker f6197 p6197 = .success := by decide +kernel
theorem unsat6197 : Unsatisfiable (PosFin 65) f6197 := by
  apply lratCheckerSound f6197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6197
  · intro a ha; simp [p6197] at ha; subst a; trivial
  · exact checked6197
theorem derived6197 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6197 := by
  apply localUnsat_implies_entails f6197 [c6194, c6139, c6195, c6196, c3793, c3796] c6197 unsat6197 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6139 := derived6139 a h
  have h2 : Entails.eval a c6195 := derived6195 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3793 := h 3792 (by decide)
  have h5 : Entails.eval a c3796 := h 3795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6198 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨45, by decide⟩, true), (⟨35, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6198 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3996, some c4625, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p6198 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6198 : lratChecker f6198 p6198 = .success := by decide +kernel
theorem unsat6198 : Unsatisfiable (PosFin 65) f6198 := by
  apply lratCheckerSound f6198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6198
  · intro a ha; simp [p6198] at ha; subst a; trivial
  · exact checked6198
theorem derived6198 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6198 := by
  apply localUnsat_implies_entails f6198 [c3996, c4625] c6198 unsat6198 (by rfl) a
  have h0 : Entails.eval a c3996 := h 3995 (by decide)
  have h1 : Entails.eval a c4625 := h 4624 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6199 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6199 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6196, some c3700, some c6197, some c6139, some c5048, some c5499, some c3602, some c5907, some c4663, some c5908, some c6013, some c4130, some c4398, some c6198, some c4535, some c4300, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6199 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6199 : lratChecker f6199 p6199 = .success := by decide +kernel
theorem unsat6199 : Unsatisfiable (PosFin 65) f6199 := by
  apply lratCheckerSound f6199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6199
  · intro a ha; simp [p6199] at ha; subst a; trivial
  · exact checked6199
theorem derived6199 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6199 := by
  apply localUnsat_implies_entails f6199 [c6194, c6196, c3700, c6197, c6139, c5048, c5499, c3602, c5907, c4663, c5908, c6013, c4130, c4398, c6198, c4535, c4300] c6199 unsat6199 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6196 := derived6196 a h
  have h2 : Entails.eval a c3700 := h 3699 (by decide)
  have h3 : Entails.eval a c6197 := derived6197 a h
  have h4 : Entails.eval a c6139 := derived6139 a h
  have h5 : Entails.eval a c5048 := h 5047 (by decide)
  have h6 : Entails.eval a c5499 := h 5498 (by decide)
  have h7 : Entails.eval a c3602 := h 3601 (by decide)
  have h8 : Entails.eval a c5907 := derived5907 a h
  have h9 : Entails.eval a c4663 := h 4662 (by decide)
  have h10 : Entails.eval a c5908 := derived5908 a h
  have h11 : Entails.eval a c6013 := derived6013 a h
  have h12 : Entails.eval a c4130 := h 4129 (by decide)
  have h13 : Entails.eval a c4398 := h 4397 (by decide)
  have h14 : Entails.eval a c6198 := derived6198 a h
  have h15 : Entails.eval a c4535 := h 4534 (by decide)
  have h16 : Entails.eval a c4300 := h 4299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6200 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6200 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6197, some c6194, some c6139, some c6196, some c3700, some c6199, some c3757, some c5591, some c4952, some c5855, some c5292, some c4722, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6200 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6200 : lratChecker f6200 p6200 = .success := by decide +kernel
theorem unsat6200 : Unsatisfiable (PosFin 65) f6200 := by
  apply lratCheckerSound f6200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6200
  · intro a ha; simp [p6200] at ha; subst a; trivial
  · exact checked6200
theorem derived6200 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6200 := by
  apply localUnsat_implies_entails f6200 [c6197, c6194, c6139, c6196, c3700, c6199, c3757, c5591, c4952, c5855, c5292, c4722] c6200 unsat6200 (by rfl) a
  have h0 : Entails.eval a c6197 := derived6197 a h
  have h1 : Entails.eval a c6194 := derived6194 a h
  have h2 : Entails.eval a c6139 := derived6139 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6199 := derived6199 a h
  have h6 : Entails.eval a c3757 := h 3756 (by decide)
  have h7 : Entails.eval a c5591 := h 5590 (by decide)
  have h8 : Entails.eval a c4952 := h 4951 (by decide)
  have h9 : Entails.eval a c5855 := h 5854 (by decide)
  have h10 : Entails.eval a c5292 := h 5291 (by decide)
  have h11 : Entails.eval a c4722 := h 4721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6201 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6201 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6200, some c6114, some c6109, some c4173, some c4037, some c4996, some c3968, some c4514, some c5106, some c3528, some c4706, some c6184, some c6148, some c5018, some c5982, some c4857, some c4755, some c6139, some c5395, some c4238, some c2830, some c2836, some c2846, some c3181, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6201 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked6201 : lratChecker f6201 p6201 = .success := by decide +kernel
theorem unsat6201 : Unsatisfiable (PosFin 65) f6201 := by
  apply lratCheckerSound f6201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6201
  · intro a ha; simp [p6201] at ha; subst a; trivial
  · exact checked6201
theorem derived6201 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6201 := by
  apply localUnsat_implies_entails f6201 [c6194, c6200, c6114, c6109, c4173, c4037, c4996, c3968, c4514, c5106, c3528, c4706, c6184, c6148, c5018, c5982, c4857, c4755, c6139, c5395, c4238, c2830, c2836, c2846, c3181] c6201 unsat6201 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6200 := derived6200 a h
  have h2 : Entails.eval a c6114 := derived6114 a h
  have h3 : Entails.eval a c6109 := derived6109 a h
  have h4 : Entails.eval a c4173 := h 4172 (by decide)
  have h5 : Entails.eval a c4037 := h 4036 (by decide)
  have h6 : Entails.eval a c4996 := h 4995 (by decide)
  have h7 : Entails.eval a c3968 := h 3967 (by decide)
  have h8 : Entails.eval a c4514 := h 4513 (by decide)
  have h9 : Entails.eval a c5106 := h 5105 (by decide)
  have h10 : Entails.eval a c3528 := h 3527 (by decide)
  have h11 : Entails.eval a c4706 := h 4705 (by decide)
  have h12 : Entails.eval a c6184 := derived6184 a h
  have h13 : Entails.eval a c6148 := derived6148 a h
  have h14 : Entails.eval a c5018 := h 5017 (by decide)
  have h15 : Entails.eval a c5982 := derived5982 a h
  have h16 : Entails.eval a c4857 := h 4856 (by decide)
  have h17 : Entails.eval a c4755 := h 4754 (by decide)
  have h18 : Entails.eval a c6139 := derived6139 a h
  have h19 : Entails.eval a c5395 := h 5394 (by decide)
  have h20 : Entails.eval a c4238 := h 4237 (by decide)
  have h21 : Entails.eval a c2830 := h 2829 (by decide)
  have h22 : Entails.eval a c2836 := h 2835 (by decide)
  have h23 : Entails.eval a c2846 := h 2845 (by decide)
  have h24 : Entails.eval a c3181 := h 3180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6202 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨28, by decide⟩, true), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨33, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6202 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6114, some c6109, some c4173, some c4037, some c4996, some c3968, some c3528, some c4706, some c3181, some c3137, some c2744, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6202 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6202 : lratChecker f6202 p6202 = .success := by decide +kernel
theorem unsat6202 : Unsatisfiable (PosFin 65) f6202 := by
  apply lratCheckerSound f6202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6202
  · intro a ha; simp [p6202] at ha; subst a; trivial
  · exact checked6202
theorem derived6202 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6202 := by
  apply localUnsat_implies_entails f6202 [c6194, c6114, c6109, c4173, c4037, c4996, c3968, c3528, c4706, c3181, c3137, c2744] c6202 unsat6202 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6114 := derived6114 a h
  have h2 : Entails.eval a c6109 := derived6109 a h
  have h3 : Entails.eval a c4173 := h 4172 (by decide)
  have h4 : Entails.eval a c4037 := h 4036 (by decide)
  have h5 : Entails.eval a c4996 := h 4995 (by decide)
  have h6 : Entails.eval a c3968 := h 3967 (by decide)
  have h7 : Entails.eval a c3528 := h 3527 (by decide)
  have h8 : Entails.eval a c4706 := h 4705 (by decide)
  have h9 : Entails.eval a c3181 := h 3180 (by decide)
  have h10 : Entails.eval a c3137 := h 3136 (by decide)
  have h11 : Entails.eval a c2744 := h 2743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6203 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨60, by decide⟩, false), (⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6203 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2712, some c2719, some c2979, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6203 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6203 : lratChecker f6203 p6203 = .success := by decide +kernel
theorem unsat6203 : Unsatisfiable (PosFin 65) f6203 := by
  apply lratCheckerSound f6203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6203
  · intro a ha; simp [p6203] at ha; subst a; trivial
  · exact checked6203
theorem derived6203 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6203 := by
  apply localUnsat_implies_entails f6203 [c2712, c2719, c2979] c6203 unsat6203 (by rfl) a
  have h0 : Entails.eval a c2712 := h 2711 (by decide)
  have h1 : Entails.eval a c2719 := h 2718 (by decide)
  have h2 : Entails.eval a c2979 := h 2978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6204 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6204 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6200, some c6114, some c6109, some c4173, some c4037, some c4996, some c3968, some c4514, some c5106, some c3528, some c4706, some c6184, some c6148, some c5018, some c5982, some c4779, some c6197, some c6139, some c4238, some c5395, some c4857, some c4756, some c4755, some c6201, some c6203, some c6202, some c2776, some c2809, some c2966, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6204 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6204 : lratChecker f6204 p6204 = .success := by decide +kernel
theorem unsat6204 : Unsatisfiable (PosFin 65) f6204 := by
  apply lratCheckerSound f6204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6204
  · intro a ha; simp [p6204] at ha; subst a; trivial
  · exact checked6204
theorem derived6204 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6204 := by
  apply localUnsat_implies_entails f6204 [c6194, c6200, c6114, c6109, c4173, c4037, c4996, c3968, c4514, c5106, c3528, c4706, c6184, c6148, c5018, c5982, c4779, c6197, c6139, c4238, c5395, c4857, c4756, c4755, c6201, c6203, c6202, c2776, c2809, c2966] c6204 unsat6204 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6200 := derived6200 a h
  have h2 : Entails.eval a c6114 := derived6114 a h
  have h3 : Entails.eval a c6109 := derived6109 a h
  have h4 : Entails.eval a c4173 := h 4172 (by decide)
  have h5 : Entails.eval a c4037 := h 4036 (by decide)
  have h6 : Entails.eval a c4996 := h 4995 (by decide)
  have h7 : Entails.eval a c3968 := h 3967 (by decide)
  have h8 : Entails.eval a c4514 := h 4513 (by decide)
  have h9 : Entails.eval a c5106 := h 5105 (by decide)
  have h10 : Entails.eval a c3528 := h 3527 (by decide)
  have h11 : Entails.eval a c4706 := h 4705 (by decide)
  have h12 : Entails.eval a c6184 := derived6184 a h
  have h13 : Entails.eval a c6148 := derived6148 a h
  have h14 : Entails.eval a c5018 := h 5017 (by decide)
  have h15 : Entails.eval a c5982 := derived5982 a h
  have h16 : Entails.eval a c4779 := h 4778 (by decide)
  have h17 : Entails.eval a c6197 := derived6197 a h
  have h18 : Entails.eval a c6139 := derived6139 a h
  have h19 : Entails.eval a c4238 := h 4237 (by decide)
  have h20 : Entails.eval a c5395 := h 5394 (by decide)
  have h21 : Entails.eval a c4857 := h 4856 (by decide)
  have h22 : Entails.eval a c4756 := h 4755 (by decide)
  have h23 : Entails.eval a c4755 := h 4754 (by decide)
  have h24 : Entails.eval a c6201 := derived6201 a h
  have h25 : Entails.eval a c6203 := derived6203 a h
  have h26 : Entails.eval a c6202 := derived6202 a h
  have h27 : Entails.eval a c2776 := h 2775 (by decide)
  have h28 : Entails.eval a c2809 := h 2808 (by decide)
  have h29 : Entails.eval a c2966 := h 2965 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6205 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6205 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6200, some c6114, some c6109, some c4173, some c4037, some c4996, some c3968, some c4514, some c5106, some c3528, some c4706, some c6184, some c6148, some c5018, some c5982, some c4779, some c6197, some c6139, some c6204, some c5051, some c4480, some c4604, some c3866, some c3823, some c6187, some c6203, some c6202, some c2776, some c2809, some c2966, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6205 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked6205 : lratChecker f6205 p6205 = .success := by decide +kernel
theorem unsat6205 : Unsatisfiable (PosFin 65) f6205 := by
  apply lratCheckerSound f6205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6205
  · intro a ha; simp [p6205] at ha; subst a; trivial
  · exact checked6205
theorem derived6205 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6205 := by
  apply localUnsat_implies_entails f6205 [c6194, c6200, c6114, c6109, c4173, c4037, c4996, c3968, c4514, c5106, c3528, c4706, c6184, c6148, c5018, c5982, c4779, c6197, c6139, c6204, c5051, c4480, c4604, c3866, c3823, c6187, c6203, c6202, c2776, c2809, c2966] c6205 unsat6205 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6200 := derived6200 a h
  have h2 : Entails.eval a c6114 := derived6114 a h
  have h3 : Entails.eval a c6109 := derived6109 a h
  have h4 : Entails.eval a c4173 := h 4172 (by decide)
  have h5 : Entails.eval a c4037 := h 4036 (by decide)
  have h6 : Entails.eval a c4996 := h 4995 (by decide)
  have h7 : Entails.eval a c3968 := h 3967 (by decide)
  have h8 : Entails.eval a c4514 := h 4513 (by decide)
  have h9 : Entails.eval a c5106 := h 5105 (by decide)
  have h10 : Entails.eval a c3528 := h 3527 (by decide)
  have h11 : Entails.eval a c4706 := h 4705 (by decide)
  have h12 : Entails.eval a c6184 := derived6184 a h
  have h13 : Entails.eval a c6148 := derived6148 a h
  have h14 : Entails.eval a c5018 := h 5017 (by decide)
  have h15 : Entails.eval a c5982 := derived5982 a h
  have h16 : Entails.eval a c4779 := h 4778 (by decide)
  have h17 : Entails.eval a c6197 := derived6197 a h
  have h18 : Entails.eval a c6139 := derived6139 a h
  have h19 : Entails.eval a c6204 := derived6204 a h
  have h20 : Entails.eval a c5051 := h 5050 (by decide)
  have h21 : Entails.eval a c4480 := h 4479 (by decide)
  have h22 : Entails.eval a c4604 := h 4603 (by decide)
  have h23 : Entails.eval a c3866 := h 3865 (by decide)
  have h24 : Entails.eval a c3823 := h 3822 (by decide)
  have h25 : Entails.eval a c6187 := derived6187 a h
  have h26 : Entails.eval a c6203 := derived6203 a h
  have h27 : Entails.eval a c6202 := derived6202 a h
  have h28 : Entails.eval a c2776 := h 2775 (by decide)
  have h29 : Entails.eval a c2809 := h 2808 (by decide)
  have h30 : Entails.eval a c2966 := h 2965 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6206 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6206 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6200, some c6114, some c6109, some c4037, some c4173, some c4996, some c5106, some c3968, some c4514, some c3528, some c4706, some c6184, some c6148, some c6205, some c5809, some c5806, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6206 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6206 : lratChecker f6206 p6206 = .success := by decide +kernel
theorem unsat6206 : Unsatisfiable (PosFin 65) f6206 := by
  apply lratCheckerSound f6206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6206
  · intro a ha; simp [p6206] at ha; subst a; trivial
  · exact checked6206
theorem derived6206 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6206 := by
  apply localUnsat_implies_entails f6206 [c6194, c6200, c6114, c6109, c4037, c4173, c4996, c5106, c3968, c4514, c3528, c4706, c6184, c6148, c6205, c5809, c5806] c6206 unsat6206 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6200 := derived6200 a h
  have h2 : Entails.eval a c6114 := derived6114 a h
  have h3 : Entails.eval a c6109 := derived6109 a h
  have h4 : Entails.eval a c4037 := h 4036 (by decide)
  have h5 : Entails.eval a c4173 := h 4172 (by decide)
  have h6 : Entails.eval a c4996 := h 4995 (by decide)
  have h7 : Entails.eval a c5106 := h 5105 (by decide)
  have h8 : Entails.eval a c3968 := h 3967 (by decide)
  have h9 : Entails.eval a c4514 := h 4513 (by decide)
  have h10 : Entails.eval a c3528 := h 3527 (by decide)
  have h11 : Entails.eval a c4706 := h 4705 (by decide)
  have h12 : Entails.eval a c6184 := derived6184 a h
  have h13 : Entails.eval a c6148 := derived6148 a h
  have h14 : Entails.eval a c6205 := derived6205 a h
  have h15 : Entails.eval a c5809 := h 5808 (by decide)
  have h16 : Entails.eval a c5806 := h 5805 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6207 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6207 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c3700, some c3796, some c5048, some c5499, some c6062, some c6067, some c5907, some c4658, some c5793, some c4349, some c3652, some c4130, some c4393, some c6070, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6207 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6207 : lratChecker f6207 p6207 = .success := by decide +kernel
theorem unsat6207 : Unsatisfiable (PosFin 65) f6207 := by
  apply lratCheckerSound f6207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6207
  · intro a ha; simp [p6207] at ha; subst a; trivial
  · exact checked6207
theorem derived6207 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6207 := by
  apply localUnsat_implies_entails f6207 [c6206, c6095, c6194, c6196, c3700, c3796, c5048, c5499, c6062, c6067, c5907, c4658, c5793, c4349, c3652, c4130, c4393, c6070] c6207 unsat6207 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c3796 := h 3795 (by decide)
  have h6 : Entails.eval a c5048 := h 5047 (by decide)
  have h7 : Entails.eval a c5499 := h 5498 (by decide)
  have h8 : Entails.eval a c6062 := derived6062 a h
  have h9 : Entails.eval a c6067 := derived6067 a h
  have h10 : Entails.eval a c5907 := derived5907 a h
  have h11 : Entails.eval a c4658 := h 4657 (by decide)
  have h12 : Entails.eval a c5793 := h 5792 (by decide)
  have h13 : Entails.eval a c4349 := h 4348 (by decide)
  have h14 : Entails.eval a c3652 := h 3651 (by decide)
  have h15 : Entails.eval a c4130 := h 4129 (by decide)
  have h16 : Entails.eval a c4393 := h 4392 (by decide)
  have h17 : Entails.eval a c6070 := derived6070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6208 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6208 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6207, some c6194, some c6206, some c6095, some c6196, some c6062, some c6067, some c3951, some c4393, some c3652, some c5370, some c6068, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6208 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6208 : lratChecker f6208 p6208 = .success := by decide +kernel
theorem unsat6208 : Unsatisfiable (PosFin 65) f6208 := by
  apply lratCheckerSound f6208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6208
  · intro a ha; simp [p6208] at ha; subst a; trivial
  · exact checked6208
theorem derived6208 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6208 := by
  apply localUnsat_implies_entails f6208 [c6207, c6194, c6206, c6095, c6196, c6062, c6067, c3951, c4393, c3652, c5370, c6068] c6208 unsat6208 (by rfl) a
  have h0 : Entails.eval a c6207 := derived6207 a h
  have h1 : Entails.eval a c6194 := derived6194 a h
  have h2 : Entails.eval a c6206 := derived6206 a h
  have h3 : Entails.eval a c6095 := derived6095 a h
  have h4 : Entails.eval a c6196 := derived6196 a h
  have h5 : Entails.eval a c6062 := derived6062 a h
  have h6 : Entails.eval a c6067 := derived6067 a h
  have h7 : Entails.eval a c3951 := h 3950 (by decide)
  have h8 : Entails.eval a c4393 := h 4392 (by decide)
  have h9 : Entails.eval a c3652 := h 3651 (by decide)
  have h10 : Entails.eval a c5370 := h 5369 (by decide)
  have h11 : Entails.eval a c6068 := derived6068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6209 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6209 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c3700, some c6208, some c4974, some c5018, some c4422, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6209 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6209 : lratChecker f6209 p6209 = .success := by decide +kernel
theorem unsat6209 : Unsatisfiable (PosFin 65) f6209 := by
  apply lratCheckerSound f6209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6209
  · intro a ha; simp [p6209] at ha; subst a; trivial
  · exact checked6209
theorem derived6209 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6209 := by
  apply localUnsat_implies_entails f6209 [c6206, c6095, c6194, c6196, c3700, c6208, c4974, c5018, c4422] c6209 unsat6209 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6208 := derived6208 a h
  have h6 : Entails.eval a c4974 := h 4973 (by decide)
  have h7 : Entails.eval a c5018 := h 5017 (by decide)
  have h8 : Entails.eval a c4422 := h 4421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6210 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6210 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c3700, some c6139, some c6207, some c6209, some c6010, some c6062, some c4974, some c5018, some c3652, some c4807, some c6013, some c6032, some c4170, some c6088, some c4366, some c5496, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6210 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked6210 : lratChecker f6210 p6210 = .success := by decide +kernel
theorem unsat6210 : Unsatisfiable (PosFin 65) f6210 := by
  apply lratCheckerSound f6210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6210
  · intro a ha; simp [p6210] at ha; subst a; trivial
  · exact checked6210
theorem derived6210 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6210 := by
  apply localUnsat_implies_entails f6210 [c6206, c6095, c6194, c6196, c3700, c6139, c6207, c6209, c6010, c6062, c4974, c5018, c3652, c4807, c6013, c6032, c4170, c6088, c4366, c5496] c6210 unsat6210 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6139 := derived6139 a h
  have h6 : Entails.eval a c6207 := derived6207 a h
  have h7 : Entails.eval a c6209 := derived6209 a h
  have h8 : Entails.eval a c6010 := derived6010 a h
  have h9 : Entails.eval a c6062 := derived6062 a h
  have h10 : Entails.eval a c4974 := h 4973 (by decide)
  have h11 : Entails.eval a c5018 := h 5017 (by decide)
  have h12 : Entails.eval a c3652 := h 3651 (by decide)
  have h13 : Entails.eval a c4807 := h 4806 (by decide)
  have h14 : Entails.eval a c6013 := derived6013 a h
  have h15 : Entails.eval a c6032 := derived6032 a h
  have h16 : Entails.eval a c4170 := h 4169 (by decide)
  have h17 : Entails.eval a c6088 := derived6088 a h
  have h18 : Entails.eval a c4366 := h 4365 (by decide)
  have h19 : Entails.eval a c5496 := h 5495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6211 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨58, by decide⟩, false), (⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6211 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6210, some c6206, some c6095, some c6194, some c6196, some c3700, some c2953, some c2969, some c2769, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6211 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6211 : lratChecker f6211 p6211 = .success := by decide +kernel
theorem unsat6211 : Unsatisfiable (PosFin 65) f6211 := by
  apply lratCheckerSound f6211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6211
  · intro a ha; simp [p6211] at ha; subst a; trivial
  · exact checked6211
theorem derived6211 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6211 := by
  apply localUnsat_implies_entails f6211 [c6210, c6206, c6095, c6194, c6196, c3700, c2953, c2969, c2769] c6211 unsat6211 (by rfl) a
  have h0 : Entails.eval a c6210 := derived6210 a h
  have h1 : Entails.eval a c6206 := derived6206 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6194 := derived6194 a h
  have h4 : Entails.eval a c6196 := derived6196 a h
  have h5 : Entails.eval a c3700 := h 3699 (by decide)
  have h6 : Entails.eval a c2953 := h 2952 (by decide)
  have h7 : Entails.eval a c2969 := h 2968 (by decide)
  have h8 : Entails.eval a c2769 := h 2768 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6212 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨28, by decide⟩, false), (⟨58, by decide⟩, false), (⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6212 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6194, some c6095, some c6196, some c3700, some c6010, some c6062, some c5018, some c4807, some c6210, some c6211, some c3322, some c3392, some c2939, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6212 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6212 : lratChecker f6212 p6212 = .success := by decide +kernel
theorem unsat6212 : Unsatisfiable (PosFin 65) f6212 := by
  apply lratCheckerSound f6212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6212
  · intro a ha; simp [p6212] at ha; subst a; trivial
  · exact checked6212
theorem derived6212 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6212 := by
  apply localUnsat_implies_entails f6212 [c6206, c6194, c6095, c6196, c3700, c6010, c6062, c5018, c4807, c6210, c6211, c3322, c3392, c2939] c6212 unsat6212 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6194 := derived6194 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c5018 := h 5017 (by decide)
  have h8 : Entails.eval a c4807 := h 4806 (by decide)
  have h9 : Entails.eval a c6210 := derived6210 a h
  have h10 : Entails.eval a c6211 := derived6211 a h
  have h11 : Entails.eval a c3322 := h 3321 (by decide)
  have h12 : Entails.eval a c3392 := h 3391 (by decide)
  have h13 : Entails.eval a c2939 := h 2938 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6213 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨58, by decide⟩, false), (⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6213 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6194, some c6095, some c6196, some c3700, some c6010, some c6062, some c5018, some c4807, some c6210, some c6212, some c2996, some c2903, some c2995, some c3122, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6213 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6213 : lratChecker f6213 p6213 = .success := by decide +kernel
theorem unsat6213 : Unsatisfiable (PosFin 65) f6213 := by
  apply lratCheckerSound f6213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6213
  · intro a ha; simp [p6213] at ha; subst a; trivial
  · exact checked6213
theorem derived6213 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6213 := by
  apply localUnsat_implies_entails f6213 [c6206, c6194, c6095, c6196, c3700, c6010, c6062, c5018, c4807, c6210, c6212, c2996, c2903, c2995, c3122] c6213 unsat6213 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6194 := derived6194 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c5018 := h 5017 (by decide)
  have h8 : Entails.eval a c4807 := h 4806 (by decide)
  have h9 : Entails.eval a c6210 := derived6210 a h
  have h10 : Entails.eval a c6212 := derived6212 a h
  have h11 : Entails.eval a c2996 := h 2995 (by decide)
  have h12 : Entails.eval a c2903 := h 2902 (by decide)
  have h13 : Entails.eval a c2995 := h 2994 (by decide)
  have h14 : Entails.eval a c3122 := h 3121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6214 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6214 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6194, some c6095, some c6196, some c3700, some c6010, some c6062, some c5018, some c4807, some c3052, some c3120, some c2874, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6214 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6214 : lratChecker f6214 p6214 = .success := by decide +kernel
theorem unsat6214 : Unsatisfiable (PosFin 65) f6214 := by
  apply lratCheckerSound f6214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6214
  · intro a ha; simp [p6214] at ha; subst a; trivial
  · exact checked6214
theorem derived6214 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6214 := by
  apply localUnsat_implies_entails f6214 [c6206, c6194, c6095, c6196, c3700, c6010, c6062, c5018, c4807, c3052, c3120, c2874] c6214 unsat6214 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6194 := derived6194 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c5018 := h 5017 (by decide)
  have h8 : Entails.eval a c4807 := h 4806 (by decide)
  have h9 : Entails.eval a c3052 := h 3051 (by decide)
  have h10 : Entails.eval a c3120 := h 3119 (by decide)
  have h11 : Entails.eval a c2874 := h 2873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6215 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨28, by decide⟩, true), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6215 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6206, some c6095, some c6196, some c6210, some c6010, some c6062, some c6140, some c3652, some c6013, some c4170, some c3700, some c5018, some c4807, some c2713, some c2981, some c3179, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6215 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6215 : lratChecker f6215 p6215 = .success := by decide +kernel
theorem unsat6215 : Unsatisfiable (PosFin 65) f6215 := by
  apply lratCheckerSound f6215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6215
  · intro a ha; simp [p6215] at ha; subst a; trivial
  · exact checked6215
theorem derived6215 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6215 := by
  apply localUnsat_implies_entails f6215 [c6194, c6206, c6095, c6196, c6210, c6010, c6062, c6140, c3652, c6013, c4170, c3700, c5018, c4807, c2713, c2981, c3179] c6215 unsat6215 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6206 := derived6206 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c6210 := derived6210 a h
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c6140 := derived6140 a h
  have h8 : Entails.eval a c3652 := h 3651 (by decide)
  have h9 : Entails.eval a c6013 := derived6013 a h
  have h10 : Entails.eval a c4170 := h 4169 (by decide)
  have h11 : Entails.eval a c3700 := h 3699 (by decide)
  have h12 : Entails.eval a c5018 := h 5017 (by decide)
  have h13 : Entails.eval a c4807 := h 4806 (by decide)
  have h14 : Entails.eval a c2713 := h 2712 (by decide)
  have h15 : Entails.eval a c2981 := h 2980 (by decide)
  have h16 : Entails.eval a c3179 := h 3178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6216 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6216 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c6210, some c6010, some c6062, some c6140, some c3700, some c5018, some c4807, some c6170, some c3652, some c6013, some c4170, some c5247, some c5483, some c5614, some c4947, some c5235, some c6213, some c4088, some c5833, some c5573, some c6215, some c6214, some c2896, some c2902, some c3254, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6216 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked6216 : lratChecker f6216 p6216 = .success := by decide +kernel
theorem unsat6216 : Unsatisfiable (PosFin 65) f6216 := by
  apply lratCheckerSound f6216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6216
  · intro a ha; simp [p6216] at ha; subst a; trivial
  · exact checked6216
theorem derived6216 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6216 := by
  apply localUnsat_implies_entails f6216 [c6206, c6095, c6194, c6196, c6210, c6010, c6062, c6140, c3700, c5018, c4807, c6170, c3652, c6013, c4170, c5247, c5483, c5614, c4947, c5235, c6213, c4088, c5833, c5573, c6215, c6214, c2896, c2902, c3254] c6216 unsat6216 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c6210 := derived6210 a h
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c6140 := derived6140 a h
  have h8 : Entails.eval a c3700 := h 3699 (by decide)
  have h9 : Entails.eval a c5018 := h 5017 (by decide)
  have h10 : Entails.eval a c4807 := h 4806 (by decide)
  have h11 : Entails.eval a c6170 := derived6170 a h
  have h12 : Entails.eval a c3652 := h 3651 (by decide)
  have h13 : Entails.eval a c6013 := derived6013 a h
  have h14 : Entails.eval a c4170 := h 4169 (by decide)
  have h15 : Entails.eval a c5247 := h 5246 (by decide)
  have h16 : Entails.eval a c5483 := h 5482 (by decide)
  have h17 : Entails.eval a c5614 := h 5613 (by decide)
  have h18 : Entails.eval a c4947 := h 4946 (by decide)
  have h19 : Entails.eval a c5235 := h 5234 (by decide)
  have h20 : Entails.eval a c6213 := derived6213 a h
  have h21 : Entails.eval a c4088 := h 4087 (by decide)
  have h22 : Entails.eval a c5833 := h 5832 (by decide)
  have h23 : Entails.eval a c5573 := h 5572 (by decide)
  have h24 : Entails.eval a c6215 := derived6215 a h
  have h25 : Entails.eval a c6214 := derived6214 a h
  have h26 : Entails.eval a c2896 := h 2895 (by decide)
  have h27 : Entails.eval a c2902 := h 2901 (by decide)
  have h28 : Entails.eval a c3254 := h 3253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6217 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, true), (⟨53, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6217 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c6210, some c6010, some c6062, some c6140, some c3652, some c6013, some c4088, some c3700, some c5018, some c4807, some c3253, some c3173, some c2710, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6217 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6217 : lratChecker f6217 p6217 = .success := by decide +kernel
theorem unsat6217 : Unsatisfiable (PosFin 65) f6217 := by
  apply lratCheckerSound f6217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6217
  · intro a ha; simp [p6217] at ha; subst a; trivial
  · exact checked6217
theorem derived6217 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6217 := by
  apply localUnsat_implies_entails f6217 [c6206, c6095, c6194, c6196, c6210, c6010, c6062, c6140, c3652, c6013, c4088, c3700, c5018, c4807, c3253, c3173, c2710] c6217 unsat6217 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c6210 := derived6210 a h
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c6140 := derived6140 a h
  have h8 : Entails.eval a c3652 := h 3651 (by decide)
  have h9 : Entails.eval a c6013 := derived6013 a h
  have h10 : Entails.eval a c4088 := h 4087 (by decide)
  have h11 : Entails.eval a c3700 := h 3699 (by decide)
  have h12 : Entails.eval a c5018 := h 5017 (by decide)
  have h13 : Entails.eval a c4807 := h 4806 (by decide)
  have h14 : Entails.eval a c3253 := h 3252 (by decide)
  have h15 : Entails.eval a c3173 := h 3172 (by decide)
  have h16 : Entails.eval a c2710 := h 2709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6218 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6218 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6194, some c6095, some c6196, some c3700, some c6010, some c6062, some c5018, some c4807, some c6210, some c3095, some c3073, some c2962, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6218 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6218 : lratChecker f6218 p6218 = .success := by decide +kernel
theorem unsat6218 : Unsatisfiable (PosFin 65) f6218 := by
  apply lratCheckerSound f6218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6218
  · intro a ha; simp [p6218] at ha; subst a; trivial
  · exact checked6218
theorem derived6218 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6218 := by
  apply localUnsat_implies_entails f6218 [c6206, c6194, c6095, c6196, c3700, c6010, c6062, c5018, c4807, c6210, c3095, c3073, c2962] c6218 unsat6218 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6194 := derived6194 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c5018 := h 5017 (by decide)
  have h8 : Entails.eval a c4807 := h 4806 (by decide)
  have h9 : Entails.eval a c6210 := derived6210 a h
  have h10 : Entails.eval a c3095 := h 3094 (by decide)
  have h11 : Entails.eval a c3073 := h 3072 (by decide)
  have h12 : Entails.eval a c2962 := h 2961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6219 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨60, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6219 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c6210, some c6010, some c6062, some c6140, some c3652, some c6013, some c4088, some c4170, some c3700, some c5018, some c4807, some c6170, some c6139, some c5247, some c4369, some c5483, some c5614, some c4947, some c5833, some c5573, some c5235, some c6213, some c6216, some c6217, some c6218, some c6214, some c2713, some c2767, some c3160, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6219 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked6219 : lratChecker f6219 p6219 = .success := by decide +kernel
theorem unsat6219 : Unsatisfiable (PosFin 65) f6219 := by
  apply lratCheckerSound f6219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6219
  · intro a ha; simp [p6219] at ha; subst a; trivial
  · exact checked6219
theorem derived6219 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6219 := by
  apply localUnsat_implies_entails f6219 [c6206, c6095, c6194, c6196, c6210, c6010, c6062, c6140, c3652, c6013, c4088, c4170, c3700, c5018, c4807, c6170, c6139, c5247, c4369, c5483, c5614, c4947, c5833, c5573, c5235, c6213, c6216, c6217, c6218, c6214, c2713, c2767, c3160] c6219 unsat6219 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c6210 := derived6210 a h
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c6140 := derived6140 a h
  have h8 : Entails.eval a c3652 := h 3651 (by decide)
  have h9 : Entails.eval a c6013 := derived6013 a h
  have h10 : Entails.eval a c4088 := h 4087 (by decide)
  have h11 : Entails.eval a c4170 := h 4169 (by decide)
  have h12 : Entails.eval a c3700 := h 3699 (by decide)
  have h13 : Entails.eval a c5018 := h 5017 (by decide)
  have h14 : Entails.eval a c4807 := h 4806 (by decide)
  have h15 : Entails.eval a c6170 := derived6170 a h
  have h16 : Entails.eval a c6139 := derived6139 a h
  have h17 : Entails.eval a c5247 := h 5246 (by decide)
  have h18 : Entails.eval a c4369 := h 4368 (by decide)
  have h19 : Entails.eval a c5483 := h 5482 (by decide)
  have h20 : Entails.eval a c5614 := h 5613 (by decide)
  have h21 : Entails.eval a c4947 := h 4946 (by decide)
  have h22 : Entails.eval a c5833 := h 5832 (by decide)
  have h23 : Entails.eval a c5573 := h 5572 (by decide)
  have h24 : Entails.eval a c5235 := h 5234 (by decide)
  have h25 : Entails.eval a c6213 := derived6213 a h
  have h26 : Entails.eval a c6216 := derived6216 a h
  have h27 : Entails.eval a c6217 := derived6217 a h
  have h28 : Entails.eval a c6218 := derived6218 a h
  have h29 : Entails.eval a c6214 := derived6214 a h
  have h30 : Entails.eval a c2713 := h 2712 (by decide)
  have h31 : Entails.eval a c2767 := h 2766 (by decide)
  have h32 : Entails.eval a c3160 := h 3159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6220 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨60, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6220 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c6210, some c6010, some c6062, some c6140, some c3700, some c5018, some c4807, some c6170, some c6219, some c5639, some c3907, some c6139, some c3784, some c5614, some c3922, some c5347, some c6213, some c3652, some c6013, some c4088, some c3228, some c3158, some c2710, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6220 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked6220 : lratChecker f6220 p6220 = .success := by decide +kernel
theorem unsat6220 : Unsatisfiable (PosFin 65) f6220 := by
  apply lratCheckerSound f6220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6220
  · intro a ha; simp [p6220] at ha; subst a; trivial
  · exact checked6220
theorem derived6220 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6220 := by
  apply localUnsat_implies_entails f6220 [c6206, c6095, c6194, c6196, c6210, c6010, c6062, c6140, c3700, c5018, c4807, c6170, c6219, c5639, c3907, c6139, c3784, c5614, c3922, c5347, c6213, c3652, c6013, c4088, c3228, c3158, c2710] c6220 unsat6220 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c6210 := derived6210 a h
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c6140 := derived6140 a h
  have h8 : Entails.eval a c3700 := h 3699 (by decide)
  have h9 : Entails.eval a c5018 := h 5017 (by decide)
  have h10 : Entails.eval a c4807 := h 4806 (by decide)
  have h11 : Entails.eval a c6170 := derived6170 a h
  have h12 : Entails.eval a c6219 := derived6219 a h
  have h13 : Entails.eval a c5639 := h 5638 (by decide)
  have h14 : Entails.eval a c3907 := h 3906 (by decide)
  have h15 : Entails.eval a c6139 := derived6139 a h
  have h16 : Entails.eval a c3784 := h 3783 (by decide)
  have h17 : Entails.eval a c5614 := h 5613 (by decide)
  have h18 : Entails.eval a c3922 := h 3921 (by decide)
  have h19 : Entails.eval a c5347 := h 5346 (by decide)
  have h20 : Entails.eval a c6213 := derived6213 a h
  have h21 : Entails.eval a c3652 := h 3651 (by decide)
  have h22 : Entails.eval a c6013 := derived6013 a h
  have h23 : Entails.eval a c4088 := h 4087 (by decide)
  have h24 : Entails.eval a c3228 := h 3227 (by decide)
  have h25 : Entails.eval a c3158 := h 3157 (by decide)
  have h26 : Entails.eval a c2710 := h 2709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6221 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6221 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c6210, some c6010, some c6062, some c6140, some c3652, some c6013, some c4088, some c4170, some c3700, some c5018, some c4807, some c6170, some c6139, some c6219, some c5639, some c3784, some c3907, some c5614, some c4317, some c5825, some c5860, some c6220, some c2742, some c2767, some c2769, some c3306, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6221 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6221 : lratChecker f6221 p6221 = .success := by decide +kernel
theorem unsat6221 : Unsatisfiable (PosFin 65) f6221 := by
  apply lratCheckerSound f6221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6221
  · intro a ha; simp [p6221] at ha; subst a; trivial
  · exact checked6221
theorem derived6221 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6221 := by
  apply localUnsat_implies_entails f6221 [c6206, c6095, c6194, c6196, c6210, c6010, c6062, c6140, c3652, c6013, c4088, c4170, c3700, c5018, c4807, c6170, c6139, c6219, c5639, c3784, c3907, c5614, c4317, c5825, c5860, c6220, c2742, c2767, c2769, c3306] c6221 unsat6221 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c6210 := derived6210 a h
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c6140 := derived6140 a h
  have h8 : Entails.eval a c3652 := h 3651 (by decide)
  have h9 : Entails.eval a c6013 := derived6013 a h
  have h10 : Entails.eval a c4088 := h 4087 (by decide)
  have h11 : Entails.eval a c4170 := h 4169 (by decide)
  have h12 : Entails.eval a c3700 := h 3699 (by decide)
  have h13 : Entails.eval a c5018 := h 5017 (by decide)
  have h14 : Entails.eval a c4807 := h 4806 (by decide)
  have h15 : Entails.eval a c6170 := derived6170 a h
  have h16 : Entails.eval a c6139 := derived6139 a h
  have h17 : Entails.eval a c6219 := derived6219 a h
  have h18 : Entails.eval a c5639 := h 5638 (by decide)
  have h19 : Entails.eval a c3784 := h 3783 (by decide)
  have h20 : Entails.eval a c3907 := h 3906 (by decide)
  have h21 : Entails.eval a c5614 := h 5613 (by decide)
  have h22 : Entails.eval a c4317 := h 4316 (by decide)
  have h23 : Entails.eval a c5825 := h 5824 (by decide)
  have h24 : Entails.eval a c5860 := h 5859 (by decide)
  have h25 : Entails.eval a c6220 := derived6220 a h
  have h26 : Entails.eval a c2742 := h 2741 (by decide)
  have h27 : Entails.eval a c2767 := h 2766 (by decide)
  have h28 : Entails.eval a c2769 := h 2768 (by decide)
  have h29 : Entails.eval a c3306 := h 3305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6222 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6222 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6206, some c6095, some c6194, some c6196, some c3700, some c6010, some c6062, some c5018, some c4807, some c6221, some c3796, some c4378, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6222 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6222 : lratChecker f6222 p6222 = .success := by decide +kernel
theorem unsat6222 : Unsatisfiable (PosFin 65) f6222 := by
  apply lratCheckerSound f6222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6222
  · intro a ha; simp [p6222] at ha; subst a; trivial
  · exact checked6222
theorem derived6222 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6222 := by
  apply localUnsat_implies_entails f6222 [c6206, c6095, c6194, c6196, c3700, c6010, c6062, c5018, c4807, c6221, c3796, c4378] c6222 unsat6222 (by rfl) a
  have h0 : Entails.eval a c6206 := derived6206 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  have h2 : Entails.eval a c6194 := derived6194 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6010 := derived6010 a h
  have h6 : Entails.eval a c6062 := derived6062 a h
  have h7 : Entails.eval a c5018 := h 5017 (by decide)
  have h8 : Entails.eval a c4807 := h 4806 (by decide)
  have h9 : Entails.eval a c6221 := derived6221 a h
  have h10 : Entails.eval a c3796 := h 3795 (by decide)
  have h11 : Entails.eval a c4378 := h 4377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6223 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨60, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6223 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6206, some c6095, some c6196, some c3700, some c3796, some c5048, some c5907, some c6067, some c6222, some c5499, some c4662, some c6198, some c4130, some c4393, some c6210, some c6062, some c3652, some c6168, some c6122, some c4924, some c3896, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6223 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked6223 : lratChecker f6223 p6223 = .success := by decide +kernel
theorem unsat6223 : Unsatisfiable (PosFin 65) f6223 := by
  apply lratCheckerSound f6223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6223
  · intro a ha; simp [p6223] at ha; subst a; trivial
  · exact checked6223
theorem derived6223 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6223 := by
  apply localUnsat_implies_entails f6223 [c6194, c6206, c6095, c6196, c3700, c3796, c5048, c5907, c6067, c6222, c5499, c4662, c6198, c4130, c4393, c6210, c6062, c3652, c6168, c6122, c4924, c3896] c6223 unsat6223 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6206 := derived6206 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c3796 := h 3795 (by decide)
  have h6 : Entails.eval a c5048 := h 5047 (by decide)
  have h7 : Entails.eval a c5907 := derived5907 a h
  have h8 : Entails.eval a c6067 := derived6067 a h
  have h9 : Entails.eval a c6222 := derived6222 a h
  have h10 : Entails.eval a c5499 := h 5498 (by decide)
  have h11 : Entails.eval a c4662 := h 4661 (by decide)
  have h12 : Entails.eval a c6198 := derived6198 a h
  have h13 : Entails.eval a c4130 := h 4129 (by decide)
  have h14 : Entails.eval a c4393 := h 4392 (by decide)
  have h15 : Entails.eval a c6210 := derived6210 a h
  have h16 : Entails.eval a c6062 := derived6062 a h
  have h17 : Entails.eval a c3652 := h 3651 (by decide)
  have h18 : Entails.eval a c6168 := derived6168 a h
  have h19 : Entails.eval a c6122 := derived6122 a h
  have h20 : Entails.eval a c4924 := h 4923 (by decide)
  have h21 : Entails.eval a c3896 := h 3895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6224 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6224 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6222, some c6206, some c6095, some c6194, some c6196, some c3700, some c6139, some c3796, some c5048, some c5499, some c6067, some c5907, some c4662, some c3652, some c4130, some c6198, some c6223, some c5280, some c4532, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6224 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked6224 : lratChecker f6224 p6224 = .success := by decide +kernel
theorem unsat6224 : Unsatisfiable (PosFin 65) f6224 := by
  apply lratCheckerSound f6224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6224
  · intro a ha; simp [p6224] at ha; subst a; trivial
  · exact checked6224
theorem derived6224 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6224 := by
  apply localUnsat_implies_entails f6224 [c6222, c6206, c6095, c6194, c6196, c3700, c6139, c3796, c5048, c5499, c6067, c5907, c4662, c3652, c4130, c6198, c6223, c5280, c4532] c6224 unsat6224 (by rfl) a
  have h0 : Entails.eval a c6222 := derived6222 a h
  have h1 : Entails.eval a c6206 := derived6206 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6194 := derived6194 a h
  have h4 : Entails.eval a c6196 := derived6196 a h
  have h5 : Entails.eval a c3700 := h 3699 (by decide)
  have h6 : Entails.eval a c6139 := derived6139 a h
  have h7 : Entails.eval a c3796 := h 3795 (by decide)
  have h8 : Entails.eval a c5048 := h 5047 (by decide)
  have h9 : Entails.eval a c5499 := h 5498 (by decide)
  have h10 : Entails.eval a c6067 := derived6067 a h
  have h11 : Entails.eval a c5907 := derived5907 a h
  have h12 : Entails.eval a c4662 := h 4661 (by decide)
  have h13 : Entails.eval a c3652 := h 3651 (by decide)
  have h14 : Entails.eval a c4130 := h 4129 (by decide)
  have h15 : Entails.eval a c6198 := derived6198 a h
  have h16 : Entails.eval a c6223 := derived6223 a h
  have h17 : Entails.eval a c5280 := h 5279 (by decide)
  have h18 : Entails.eval a c4532 := h 4531 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6225 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨36, by decide⟩, false), (⟨60, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6225 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3750, some c3784, some c4948, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6225 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6225 : lratChecker f6225 p6225 = .success := by decide +kernel
theorem unsat6225 : Unsatisfiable (PosFin 65) f6225 := by
  apply lratCheckerSound f6225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6225
  · intro a ha; simp [p6225] at ha; subst a; trivial
  · exact checked6225
theorem derived6225 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6225 := by
  apply localUnsat_implies_entails f6225 [c3750, c3784, c4948] c6225 unsat6225 (by rfl) a
  have h0 : Entails.eval a c3750 := h 3749 (by decide)
  have h1 : Entails.eval a c3784 := h 3783 (by decide)
  have h2 : Entails.eval a c4948 := h 4947 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6226 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6226 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6224, some c6222, some c6206, some c6095, some c6194, some c6196, some c3700, some c6139, some c6225, some c3747, some c4002, some c5292, some c3957, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6226 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6226 : lratChecker f6226 p6226 = .success := by decide +kernel
theorem unsat6226 : Unsatisfiable (PosFin 65) f6226 := by
  apply lratCheckerSound f6226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6226
  · intro a ha; simp [p6226] at ha; subst a; trivial
  · exact checked6226
theorem derived6226 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6226 := by
  apply localUnsat_implies_entails f6226 [c6224, c6222, c6206, c6095, c6194, c6196, c3700, c6139, c6225, c3747, c4002, c5292, c3957] c6226 unsat6226 (by rfl) a
  have h0 : Entails.eval a c6224 := derived6224 a h
  have h1 : Entails.eval a c6222 := derived6222 a h
  have h2 : Entails.eval a c6206 := derived6206 a h
  have h3 : Entails.eval a c6095 := derived6095 a h
  have h4 : Entails.eval a c6194 := derived6194 a h
  have h5 : Entails.eval a c6196 := derived6196 a h
  have h6 : Entails.eval a c3700 := h 3699 (by decide)
  have h7 : Entails.eval a c6139 := derived6139 a h
  have h8 : Entails.eval a c6225 := derived6225 a h
  have h9 : Entails.eval a c3747 := h 3746 (by decide)
  have h10 : Entails.eval a c4002 := h 4001 (by decide)
  have h11 : Entails.eval a c5292 := h 5291 (by decide)
  have h12 : Entails.eval a c3957 := h 3956 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6227 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6227 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6194, some c6206, some c6095, some c6196, some c3700, some c6226, some c4807, some c4831, some c5476, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6227 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6227 : lratChecker f6227 p6227 = .success := by decide +kernel
theorem unsat6227 : Unsatisfiable (PosFin 65) f6227 := by
  apply lratCheckerSound f6227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6227
  · intro a ha; simp [p6227] at ha; subst a; trivial
  · exact checked6227
theorem derived6227 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6227 := by
  apply localUnsat_implies_entails f6227 [c6194, c6206, c6095, c6196, c3700, c6226, c4807, c4831, c5476] c6227 unsat6227 (by rfl) a
  have h0 : Entails.eval a c6194 := derived6194 a h
  have h1 : Entails.eval a c6206 := derived6206 a h
  have h2 : Entails.eval a c6095 := derived6095 a h
  have h3 : Entails.eval a c6196 := derived6196 a h
  have h4 : Entails.eval a c3700 := h 3699 (by decide)
  have h5 : Entails.eval a c6226 := derived6226 a h
  have h6 : Entails.eval a c4807 := h 4806 (by decide)
  have h7 : Entails.eval a c4831 := h 4830 (by decide)
  have h8 : Entails.eval a c5476 := h 5475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6228 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6228 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5473, some c5471, some c5470, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6228 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6228 : lratChecker f6228 p6228 = .success := by decide +kernel
theorem unsat6228 : Unsatisfiable (PosFin 65) f6228 := by
  apply lratCheckerSound f6228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6228
  · intro a ha; simp [p6228] at ha; subst a; trivial
  · exact checked6228
theorem derived6228 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6228 := by
  apply localUnsat_implies_entails f6228 [c6227, c5473, c5471, c5470] c6228 unsat6228 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5473 := h 5472 (by decide)
  have h2 : Entails.eval a c5471 := h 5470 (by decide)
  have h3 : Entails.eval a c5470 := h 5469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6229 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨59, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6229 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4826, some c4823, some c4819, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6229 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6229 : lratChecker f6229 p6229 = .success := by decide +kernel
theorem unsat6229 : Unsatisfiable (PosFin 65) f6229 := by
  apply lratCheckerSound f6229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6229
  · intro a ha; simp [p6229] at ha; subst a; trivial
  · exact checked6229
theorem derived6229 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6229 := by
  apply localUnsat_implies_entails f6229 [c6227, c4826, c4823, c4819] c6229 unsat6229 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4826 := h 4825 (by decide)
  have h2 : Entails.eval a c4823 := h 4822 (by decide)
  have h3 : Entails.eval a c4819 := h 4818 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6230 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨59, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6230 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4797, some c4801, some c4793, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6230 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6230 : lratChecker f6230 p6230 = .success := by decide +kernel
theorem unsat6230 : Unsatisfiable (PosFin 65) f6230 := by
  apply lratCheckerSound f6230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6230
  · intro a ha; simp [p6230] at ha; subst a; trivial
  · exact checked6230
theorem derived6230 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6230 := by
  apply localUnsat_implies_entails f6230 [c6227, c4797, c4801, c4793] c6230 unsat6230 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4797 := h 4796 (by decide)
  have h2 : Entails.eval a c4801 := h 4800 (by decide)
  have h3 : Entails.eval a c4793 := h 4792 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6231 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6231 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6229, some c6230, some c6228, some c3692, some c3683, some c3681, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6231 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6231 : lratChecker f6231 p6231 = .success := by decide +kernel
theorem unsat6231 : Unsatisfiable (PosFin 65) f6231 := by
  apply lratCheckerSound f6231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6231
  · intro a ha; simp [p6231] at ha; subst a; trivial
  · exact checked6231
theorem derived6231 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6231 := by
  apply localUnsat_implies_entails f6231 [c6227, c6229, c6230, c6228, c3692, c3683, c3681] c6231 unsat6231 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6229 := derived6229 a h
  have h2 : Entails.eval a c6230 := derived6230 a h
  have h3 : Entails.eval a c6228 := derived6228 a h
  have h4 : Entails.eval a c3692 := h 3691 (by decide)
  have h5 : Entails.eval a c3683 := h 3682 (by decide)
  have h6 : Entails.eval a c3681 := h 3680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6232 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6232 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3691, some c3681, some c3682, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6232 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6232 : lratChecker f6232 p6232 = .success := by decide +kernel
theorem unsat6232 : Unsatisfiable (PosFin 65) f6232 := by
  apply lratCheckerSound f6232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6232
  · intro a ha; simp [p6232] at ha; subst a; trivial
  · exact checked6232
theorem derived6232 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6232 := by
  apply localUnsat_implies_entails f6232 [c6227, c3691, c3681, c3682] c6232 unsat6232 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3691 := h 3690 (by decide)
  have h2 : Entails.eval a c3681 := h 3680 (by decide)
  have h3 : Entails.eval a c3682 := h 3681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6233 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6233 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6232, some c4741, some c3684, some c3699, some c4739, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6233 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6233 : lratChecker f6233 p6233 = .success := by decide +kernel
theorem unsat6233 : Unsatisfiable (PosFin 65) f6233 := by
  apply lratCheckerSound f6233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6233
  · intro a ha; simp [p6233] at ha; subst a; trivial
  · exact checked6233
theorem derived6233 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6233 := by
  apply localUnsat_implies_entails f6233 [c6227, c6232, c4741, c3684, c3699, c4739] c6233 unsat6233 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6232 := derived6232 a h
  have h2 : Entails.eval a c4741 := h 4740 (by decide)
  have h3 : Entails.eval a c3684 := h 3683 (by decide)
  have h4 : Entails.eval a c3699 := h 3698 (by decide)
  have h5 : Entails.eval a c4739 := h 4738 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6234 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6234 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6233, some c6231, some c6227, some c3747, some c4799, some c4826, some c5474, some c5464, some c5472, some c5475, some c3779, some c5594, some c5571, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6234 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6234 : lratChecker f6234 p6234 = .success := by decide +kernel
theorem unsat6234 : Unsatisfiable (PosFin 65) f6234 := by
  apply lratCheckerSound f6234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6234
  · intro a ha; simp [p6234] at ha; subst a; trivial
  · exact checked6234
theorem derived6234 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6234 := by
  apply localUnsat_implies_entails f6234 [c6233, c6231, c6227, c3747, c4799, c4826, c5474, c5464, c5472, c5475, c3779, c5594, c5571] c6234 unsat6234 (by rfl) a
  have h0 : Entails.eval a c6233 := derived6233 a h
  have h1 : Entails.eval a c6231 := derived6231 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c3747 := h 3746 (by decide)
  have h4 : Entails.eval a c4799 := h 4798 (by decide)
  have h5 : Entails.eval a c4826 := h 4825 (by decide)
  have h6 : Entails.eval a c5474 := h 5473 (by decide)
  have h7 : Entails.eval a c5464 := h 5463 (by decide)
  have h8 : Entails.eval a c5472 := h 5471 (by decide)
  have h9 : Entails.eval a c5475 := h 5474 (by decide)
  have h10 : Entails.eval a c3779 := h 3778 (by decide)
  have h11 : Entails.eval a c5594 := h 5593 (by decide)
  have h12 : Entails.eval a c5571 := h 5570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6235 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6235 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6233, some c3754, some c4804, some c5005, some c4135, some c5288, some c3641, some c5757, some c4061, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6235 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6235 : lratChecker f6235 p6235 = .success := by decide +kernel
theorem unsat6235 : Unsatisfiable (PosFin 65) f6235 := by
  apply lratCheckerSound f6235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6235
  · intro a ha; simp [p6235] at ha; subst a; trivial
  · exact checked6235
theorem derived6235 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6235 := by
  apply localUnsat_implies_entails f6235 [c6233, c3754, c4804, c5005, c4135, c5288, c3641, c5757, c4061] c6235 unsat6235 (by rfl) a
  have h0 : Entails.eval a c6233 := derived6233 a h
  have h1 : Entails.eval a c3754 := h 3753 (by decide)
  have h2 : Entails.eval a c4804 := h 4803 (by decide)
  have h3 : Entails.eval a c5005 := h 5004 (by decide)
  have h4 : Entails.eval a c4135 := h 4134 (by decide)
  have h5 : Entails.eval a c5288 := h 5287 (by decide)
  have h6 : Entails.eval a c3641 := h 3640 (by decide)
  have h7 : Entails.eval a c5757 := h 5756 (by decide)
  have h8 : Entails.eval a c4061 := h 4060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6236 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨34, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6236 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5469, some c4157, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6236 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6236 : lratChecker f6236 p6236 = .success := by decide +kernel
theorem unsat6236 : Unsatisfiable (PosFin 65) f6236 := by
  apply lratCheckerSound f6236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6236
  · intro a ha; simp [p6236] at ha; subst a; trivial
  · exact checked6236
theorem derived6236 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6236 := by
  apply localUnsat_implies_entails f6236 [c5469, c4157] c6236 unsat6236 (by rfl) a
  have h0 : Entails.eval a c5469 := h 5468 (by decide)
  have h1 : Entails.eval a c4157 := h 4156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6237 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6237 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6234, some c6233, some c6231, some c6227, some c6235, some c4800, some c4119, some c3783, some c6236, some c5585, some c3745, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6237 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6237 : lratChecker f6237 p6237 = .success := by decide +kernel
theorem unsat6237 : Unsatisfiable (PosFin 65) f6237 := by
  apply lratCheckerSound f6237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6237
  · intro a ha; simp [p6237] at ha; subst a; trivial
  · exact checked6237
theorem derived6237 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6237 := by
  apply localUnsat_implies_entails f6237 [c6234, c6233, c6231, c6227, c6235, c4800, c4119, c3783, c6236, c5585, c3745] c6237 unsat6237 (by rfl) a
  have h0 : Entails.eval a c6234 := derived6234 a h
  have h1 : Entails.eval a c6233 := derived6233 a h
  have h2 : Entails.eval a c6231 := derived6231 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6235 := derived6235 a h
  have h5 : Entails.eval a c4800 := h 4799 (by decide)
  have h6 : Entails.eval a c4119 := h 4118 (by decide)
  have h7 : Entails.eval a c3783 := h 3782 (by decide)
  have h8 : Entails.eval a c6236 := derived6236 a h
  have h9 : Entails.eval a c5585 := h 5584 (by decide)
  have h10 : Entails.eval a c3745 := h 3744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6238 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6238 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6233, some c6234, some c6237, some c4793, some c4819, some c5470, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6238 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6238 : lratChecker f6238 p6238 = .success := by decide +kernel
theorem unsat6238 : Unsatisfiable (PosFin 65) f6238 := by
  apply lratCheckerSound f6238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6238
  · intro a ha; simp [p6238] at ha; subst a; trivial
  · exact checked6238
theorem derived6238 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6238 := by
  apply localUnsat_implies_entails f6238 [c6227, c6233, c6234, c6237, c4793, c4819, c5470] c6238 unsat6238 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6233 := derived6233 a h
  have h2 : Entails.eval a c6234 := derived6234 a h
  have h3 : Entails.eval a c6237 := derived6237 a h
  have h4 : Entails.eval a c4793 := h 4792 (by decide)
  have h5 : Entails.eval a c4819 := h 4818 (by decide)
  have h6 : Entails.eval a c5470 := h 5469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6239 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨59, by decide⟩, true), (⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨58, by decide⟩, true), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6239 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5008, some c4407, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p6239 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6239 : lratChecker f6239 p6239 = .success := by decide +kernel
theorem unsat6239 : Unsatisfiable (PosFin 65) f6239 := by
  apply lratCheckerSound f6239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6239
  · intro a ha; simp [p6239] at ha; subst a; trivial
  · exact checked6239
theorem derived6239 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6239 := by
  apply localUnsat_implies_entails f6239 [c5008, c4407] c6239 unsat6239 (by rfl) a
  have h0 : Entails.eval a c5008 := h 5007 (by decide)
  have h1 : Entails.eval a c4407 := h 4406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6240 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨52, by decide⟩, false), (⟨46, by decide⟩, true), (⟨35, by decide⟩, true), (⟨58, by decide⟩, true), (⟨44, by decide⟩, true), (⟨34, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6240 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3949, some c5221, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6240 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6240 : lratChecker f6240 p6240 = .success := by decide +kernel
theorem unsat6240 : Unsatisfiable (PosFin 65) f6240 := by
  apply lratCheckerSound f6240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6240
  · intro a ha; simp [p6240] at ha; subst a; trivial
  · exact checked6240
theorem derived6240 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6240 := by
  apply localUnsat_implies_entails f6240 [c6227, c3949, c5221] c6240 unsat6240 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3949 := h 3948 (by decide)
  have h2 : Entails.eval a c5221 := h 5220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6241 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨46, by decide⟩, true), (⟨38, by decide⟩, false), (⟨35, by decide⟩, true), (⟨58, by decide⟩, true), (⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨34, by decide⟩, true), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6241 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6240, some c5065, some c4966, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6241 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6241 : lratChecker f6241 p6241 = .success := by decide +kernel
theorem unsat6241 : Unsatisfiable (PosFin 65) f6241 := by
  apply lratCheckerSound f6241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6241
  · intro a ha; simp [p6241] at ha; subst a; trivial
  · exact checked6241
theorem derived6241 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6241 := by
  apply localUnsat_implies_entails f6241 [c6227, c6240, c5065, c4966] c6241 unsat6241 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6240 := derived6240 a h
  have h2 : Entails.eval a c5065 := h 5064 (by decide)
  have h3 : Entails.eval a c4966 := h 4965 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6242 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨56, by decide⟩, false), (⟨59, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6242 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2750, some c2762, some c2772, some c3328, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p6242 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6242 : lratChecker f6242 p6242 = .success := by decide +kernel
theorem unsat6242 : Unsatisfiable (PosFin 65) f6242 := by
  apply lratCheckerSound f6242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6242
  · intro a ha; simp [p6242] at ha; subst a; trivial
  · exact checked6242
theorem derived6242 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6242 := by
  apply localUnsat_implies_entails f6242 [c2750, c2762, c2772, c3328] c6242 unsat6242 (by rfl) a
  have h0 : Entails.eval a c2750 := h 2749 (by decide)
  have h1 : Entails.eval a c2762 := h 2761 (by decide)
  have h2 : Entails.eval a c2772 := h 2771 (by decide)
  have h3 : Entails.eval a c3328 := h 3327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6243 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨38, by decide⟩, false), (⟨58, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6243 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3328, some c3207, some c3143, some c3136, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6243 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6243 : lratChecker f6243 p6243 = .success := by decide +kernel
theorem unsat6243 : Unsatisfiable (PosFin 65) f6243 := by
  apply lratCheckerSound f6243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6243
  · intro a ha; simp [p6243] at ha; subst a; trivial
  · exact checked6243
theorem derived6243 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6243 := by
  apply localUnsat_implies_entails f6243 [c3328, c3207, c3143, c3136] c6243 unsat6243 (by rfl) a
  have h0 : Entails.eval a c3328 := h 3327 (by decide)
  have h1 : Entails.eval a c3207 := h 3206 (by decide)
  have h2 : Entails.eval a c3143 := h 3142 (by decide)
  have h3 : Entails.eval a c3136 := h 3135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6244 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨37, by decide⟩, false), (⟨59, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨58, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6244 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5044, some c6243, some c2881, some c3213, some c3380, some c3383, some c3274, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6244 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6244 : lratChecker f6244 p6244 = .success := by decide +kernel
theorem unsat6244 : Unsatisfiable (PosFin 65) f6244 := by
  apply lratCheckerSound f6244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6244
  · intro a ha; simp [p6244] at ha; subst a; trivial
  · exact checked6244
theorem derived6244 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6244 := by
  apply localUnsat_implies_entails f6244 [c6227, c5044, c6243, c2881, c3213, c3380, c3383, c3274] c6244 unsat6244 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5044 := h 5043 (by decide)
  have h2 : Entails.eval a c6243 := derived6243 a h
  have h3 : Entails.eval a c2881 := h 2880 (by decide)
  have h4 : Entails.eval a c3213 := h 3212 (by decide)
  have h5 : Entails.eval a c3380 := h 3379 (by decide)
  have h6 : Entails.eval a c3383 := h 3382 (by decide)
  have h7 : Entails.eval a c3274 := h 3273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6245 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨47, by decide⟩, true), (⟨58, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6245 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4484, some c4113, some c5675, some c3959, some c5321, some c6241, some c6239, some c4628, some c4331, some c5063, some c5065, some c5044, some c5078, some c5056, some c4978, some c5232, some c6242, some c6244, some c2788, some c2791, some c3367, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6245 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked6245 : lratChecker f6245 p6245 = .success := by decide +kernel
theorem unsat6245 : Unsatisfiable (PosFin 65) f6245 := by
  apply lratCheckerSound f6245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6245
  · intro a ha; simp [p6245] at ha; subst a; trivial
  · exact checked6245
theorem derived6245 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6245 := by
  apply localUnsat_implies_entails f6245 [c6227, c4484, c4113, c5675, c3959, c5321, c6241, c6239, c4628, c4331, c5063, c5065, c5044, c5078, c5056, c4978, c5232, c6242, c6244, c2788, c2791, c3367] c6245 unsat6245 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4484 := h 4483 (by decide)
  have h2 : Entails.eval a c4113 := h 4112 (by decide)
  have h3 : Entails.eval a c5675 := h 5674 (by decide)
  have h4 : Entails.eval a c3959 := h 3958 (by decide)
  have h5 : Entails.eval a c5321 := h 5320 (by decide)
  have h6 : Entails.eval a c6241 := derived6241 a h
  have h7 : Entails.eval a c6239 := derived6239 a h
  have h8 : Entails.eval a c4628 := h 4627 (by decide)
  have h9 : Entails.eval a c4331 := h 4330 (by decide)
  have h10 : Entails.eval a c5063 := h 5062 (by decide)
  have h11 : Entails.eval a c5065 := h 5064 (by decide)
  have h12 : Entails.eval a c5044 := h 5043 (by decide)
  have h13 : Entails.eval a c5078 := h 5077 (by decide)
  have h14 : Entails.eval a c5056 := h 5055 (by decide)
  have h15 : Entails.eval a c4978 := h 4977 (by decide)
  have h16 : Entails.eval a c5232 := h 5231 (by decide)
  have h17 : Entails.eval a c6242 := derived6242 a h
  have h18 : Entails.eval a c6244 := derived6244 a h
  have h19 : Entails.eval a c2788 := h 2787 (by decide)
  have h20 : Entails.eval a c2791 := h 2790 (by decide)
  have h21 : Entails.eval a c3367 := h 3366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6246 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨37, by decide⟩, true), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6246 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2788, some c2791, some c3366, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p6246 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6246 : lratChecker f6246 p6246 = .success := by decide +kernel
theorem unsat6246 : Unsatisfiable (PosFin 65) f6246 := by
  apply lratCheckerSound f6246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6246
  · intro a ha; simp [p6246] at ha; subst a; trivial
  · exact checked6246
theorem derived6246 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6246 := by
  apply localUnsat_implies_entails f6246 [c2788, c2791, c3366] c6246 unsat6246 (by rfl) a
  have h0 : Entails.eval a c2788 := h 2787 (by decide)
  have h1 : Entails.eval a c2791 := h 2790 (by decide)
  have h2 : Entails.eval a c3366 := h 3365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6247 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨54, by decide⟩, false), (⟨23, by decide⟩, true), (⟨37, by decide⟩, true), (⟨59, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨34, by decide⟩, true), (⟨39, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6247 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2957, some c3165, some c3363, some c2918, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6247 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6247 : lratChecker f6247 p6247 = .success := by decide +kernel
theorem unsat6247 : Unsatisfiable (PosFin 65) f6247 := by
  apply lratCheckerSound f6247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6247
  · intro a ha; simp [p6247] at ha; subst a; trivial
  · exact checked6247
theorem derived6247 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6247 := by
  apply localUnsat_implies_entails f6247 [c2957, c3165, c3363, c2918] c6247 unsat6247 (by rfl) a
  have h0 : Entails.eval a c2957 := h 2956 (by decide)
  have h1 : Entails.eval a c3165 := h 3164 (by decide)
  have h2 : Entails.eval a c3363 := h 3362 (by decide)
  have h3 : Entails.eval a c2918 := h 2917 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6248 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6248 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6227, some c4113, some c5470, some c4860, some c5675, some c4484, some c3959, some c5321, some c6241, some c4331, some c4628, some c6239, some c6245, some c3949, some c3598, some c4651, some c3945, some c4044, some c5208, some c6242, some c4647, some c6246, some c6247, some c2779, some c2815, some c3384, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6248 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked6248 : lratChecker f6248 p6248 = .success := by decide +kernel
theorem unsat6248 : Unsatisfiable (PosFin 65) f6248 := by
  apply lratCheckerSound f6248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6248
  · intro a ha; simp [p6248] at ha; subst a; trivial
  · exact checked6248
theorem derived6248 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6248 := by
  apply localUnsat_implies_entails f6248 [c6238, c6227, c4113, c5470, c4860, c5675, c4484, c3959, c5321, c6241, c4331, c4628, c6239, c6245, c3949, c3598, c4651, c3945, c4044, c5208, c6242, c4647, c6246, c6247, c2779, c2815, c3384] c6248 unsat6248 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4113 := h 4112 (by decide)
  have h3 : Entails.eval a c5470 := h 5469 (by decide)
  have h4 : Entails.eval a c4860 := h 4859 (by decide)
  have h5 : Entails.eval a c5675 := h 5674 (by decide)
  have h6 : Entails.eval a c4484 := h 4483 (by decide)
  have h7 : Entails.eval a c3959 := h 3958 (by decide)
  have h8 : Entails.eval a c5321 := h 5320 (by decide)
  have h9 : Entails.eval a c6241 := derived6241 a h
  have h10 : Entails.eval a c4331 := h 4330 (by decide)
  have h11 : Entails.eval a c4628 := h 4627 (by decide)
  have h12 : Entails.eval a c6239 := derived6239 a h
  have h13 : Entails.eval a c6245 := derived6245 a h
  have h14 : Entails.eval a c3949 := h 3948 (by decide)
  have h15 : Entails.eval a c3598 := h 3597 (by decide)
  have h16 : Entails.eval a c4651 := h 4650 (by decide)
  have h17 : Entails.eval a c3945 := h 3944 (by decide)
  have h18 : Entails.eval a c4044 := h 4043 (by decide)
  have h19 : Entails.eval a c5208 := h 5207 (by decide)
  have h20 : Entails.eval a c6242 := derived6242 a h
  have h21 : Entails.eval a c4647 := h 4646 (by decide)
  have h22 : Entails.eval a c6246 := derived6246 a h
  have h23 : Entails.eval a c6247 := derived6247 a h
  have h24 : Entails.eval a c2779 := h 2778 (by decide)
  have h25 : Entails.eval a c2815 := h 2814 (by decide)
  have h26 : Entails.eval a c3384 := h 3383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6249 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6249 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6238, some c5470, some c4860, some c5675, some c4113, some c4484, some c3959, some c5321, some c4331, some c6241, some c6248, some c5585, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6249 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6249 : lratChecker f6249 p6249 = .success := by decide +kernel
theorem unsat6249 : Unsatisfiable (PosFin 65) f6249 := by
  apply lratCheckerSound f6249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6249
  · intro a ha; simp [p6249] at ha; subst a; trivial
  · exact checked6249
theorem derived6249 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6249 := by
  apply localUnsat_implies_entails f6249 [c6227, c6238, c5470, c4860, c5675, c4113, c4484, c3959, c5321, c4331, c6241, c6248, c5585] c6249 unsat6249 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6238 := derived6238 a h
  have h2 : Entails.eval a c5470 := h 5469 (by decide)
  have h3 : Entails.eval a c4860 := h 4859 (by decide)
  have h4 : Entails.eval a c5675 := h 5674 (by decide)
  have h5 : Entails.eval a c4113 := h 4112 (by decide)
  have h6 : Entails.eval a c4484 := h 4483 (by decide)
  have h7 : Entails.eval a c3959 := h 3958 (by decide)
  have h8 : Entails.eval a c5321 := h 5320 (by decide)
  have h9 : Entails.eval a c4331 := h 4330 (by decide)
  have h10 : Entails.eval a c6241 := derived6241 a h
  have h11 : Entails.eval a c6248 := derived6248 a h
  have h12 : Entails.eval a c5585 := h 5584 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6250 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6250 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6227, some c5470, some c4860, some c5675, some c6249, some c5074, some c4683, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6250 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6250 : lratChecker f6250 p6250 = .success := by decide +kernel
theorem unsat6250 : Unsatisfiable (PosFin 65) f6250 := by
  apply lratCheckerSound f6250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6250
  · intro a ha; simp [p6250] at ha; subst a; trivial
  · exact checked6250
theorem derived6250 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6250 := by
  apply localUnsat_implies_entails f6250 [c6238, c6227, c5470, c4860, c5675, c6249, c5074, c4683] c6250 unsat6250 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5470 := h 5469 (by decide)
  have h3 : Entails.eval a c4860 := h 4859 (by decide)
  have h4 : Entails.eval a c5675 := h 5674 (by decide)
  have h5 : Entails.eval a c6249 := derived6249 a h
  have h6 : Entails.eval a c5074 := h 5073 (by decide)
  have h7 : Entails.eval a c4683 := h 4682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6251 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨58, by decide⟩, false), (⟨53, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5679, some c5074, some c4683, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6251 : lratChecker f6251 p6251 = .success := by decide +kernel
theorem unsat6251 : Unsatisfiable (PosFin 65) f6251 := by
  apply lratCheckerSound f6251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6251
  · intro a ha; simp [p6251] at ha; subst a; trivial
  · exact checked6251
theorem derived6251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6251 := by
  apply localUnsat_implies_entails f6251 [c5679, c5074, c4683] c6251 unsat6251 (by rfl) a
  have h0 : Entails.eval a c5679 := h 5678 (by decide)
  have h1 : Entails.eval a c5074 := h 5073 (by decide)
  have h2 : Entails.eval a c4683 := h 4682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6252 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6251, some c4721, some c4866, some c5273, some c5269, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6252 : lratChecker f6252 p6252 = .success := by decide +kernel
theorem unsat6252 : Unsatisfiable (PosFin 65) f6252 := by
  apply lratCheckerSound f6252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6252
  · intro a ha; simp [p6252] at ha; subst a; trivial
  · exact checked6252
theorem derived6252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6252 := by
  apply localUnsat_implies_entails f6252 [c6227, c6251, c4721, c4866, c5273, c5269] c6252 unsat6252 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6251 := derived6251 a h
  have h2 : Entails.eval a c4721 := h 4720 (by decide)
  have h3 : Entails.eval a c4866 := h 4865 (by decide)
  have h4 : Entails.eval a c5273 := h 5272 (by decide)
  have h5 : Entails.eval a c5269 := h 5268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6253 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5472, some c5474, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6253 : lratChecker f6253 p6253 = .success := by decide +kernel
theorem unsat6253 : Unsatisfiable (PosFin 65) f6253 := by
  apply lratCheckerSound f6253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6253
  · intro a ha; simp [p6253] at ha; subst a; trivial
  · exact checked6253
theorem derived6253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6253 := by
  apply localUnsat_implies_entails f6253 [c6227, c5472, c5474] c6253 unsat6253 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5472 := h 5471 (by decide)
  have h2 : Entails.eval a c5474 := h 5473 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6254 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, true), (⟨45, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2782, some c2794, some c2817, some c3384, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6254 : lratChecker f6254 p6254 = .success := by decide +kernel
theorem unsat6254 : Unsatisfiable (PosFin 65) f6254 := by
  apply lratCheckerSound f6254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6254
  · intro a ha; simp [p6254] at ha; subst a; trivial
  · exact checked6254
theorem derived6254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6254 := by
  apply localUnsat_implies_entails f6254 [c2782, c2794, c2817, c3384] c6254 unsat6254 (by rfl) a
  have h0 : Entails.eval a c2782 := h 2781 (by decide)
  have h1 : Entails.eval a c2794 := h 2793 (by decide)
  have h2 : Entails.eval a c2817 := h 2816 (by decide)
  have h3 : Entails.eval a c3384 := h 3383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6255 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨61, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6250, some c6252, some c6253, some c4866, some c4483, some c4121, some c3957, some c5293, some c5679, some c5332, some c6241, some c6239, some c4634, some c6227, some c3598, some c4651, some c4329, some c5208, some c4647, some c6254, some c6247, some c2752, some c2764, some c2775, some c3334, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked6255 : lratChecker f6255 p6255 = .success := by decide +kernel
theorem unsat6255 : Unsatisfiable (PosFin 65) f6255 := by
  apply lratCheckerSound f6255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6255
  · intro a ha; simp [p6255] at ha; subst a; trivial
  · exact checked6255
theorem derived6255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6255 := by
  apply localUnsat_implies_entails f6255 [c6238, c6250, c6252, c6253, c4866, c4483, c4121, c3957, c5293, c5679, c5332, c6241, c6239, c4634, c6227, c3598, c4651, c4329, c5208, c4647, c6254, c6247, c2752, c2764, c2775, c3334] c6255 unsat6255 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6250 := derived6250 a h
  have h2 : Entails.eval a c6252 := derived6252 a h
  have h3 : Entails.eval a c6253 := derived6253 a h
  have h4 : Entails.eval a c4866 := h 4865 (by decide)
  have h5 : Entails.eval a c4483 := h 4482 (by decide)
  have h6 : Entails.eval a c4121 := h 4120 (by decide)
  have h7 : Entails.eval a c3957 := h 3956 (by decide)
  have h8 : Entails.eval a c5293 := h 5292 (by decide)
  have h9 : Entails.eval a c5679 := h 5678 (by decide)
  have h10 : Entails.eval a c5332 := h 5331 (by decide)
  have h11 : Entails.eval a c6241 := derived6241 a h
  have h12 : Entails.eval a c6239 := derived6239 a h
  have h13 : Entails.eval a c4634 := h 4633 (by decide)
  have h14 : Entails.eval a c6227 := derived6227 a h
  have h15 : Entails.eval a c3598 := h 3597 (by decide)
  have h16 : Entails.eval a c4651 := h 4650 (by decide)
  have h17 : Entails.eval a c4329 := h 4328 (by decide)
  have h18 : Entails.eval a c5208 := h 5207 (by decide)
  have h19 : Entails.eval a c4647 := h 4646 (by decide)
  have h20 : Entails.eval a c6254 := derived6254 a h
  have h21 : Entails.eval a c6247 := derived6247 a h
  have h22 : Entails.eval a c2752 := h 2751 (by decide)
  have h23 : Entails.eval a c2764 := h 2763 (by decide)
  have h24 : Entails.eval a c2775 := h 2774 (by decide)
  have h25 : Entails.eval a c3334 := h 3333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6256 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨56, by decide⟩, false), (⟨59, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2752, some c2764, some c2775, some c3334, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p6256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6256 : lratChecker f6256 p6256 = .success := by decide +kernel
theorem unsat6256 : Unsatisfiable (PosFin 65) f6256 := by
  apply lratCheckerSound f6256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6256
  · intro a ha; simp [p6256] at ha; subst a; trivial
  · exact checked6256
theorem derived6256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6256 := by
  apply localUnsat_implies_entails f6256 [c2752, c2764, c2775, c3334] c6256 unsat6256 (by rfl) a
  have h0 : Entails.eval a c2752 := h 2751 (by decide)
  have h1 : Entails.eval a c2764 := h 2763 (by decide)
  have h2 : Entails.eval a c2775 := h 2774 (by decide)
  have h3 : Entails.eval a c3334 := h 3333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6257 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨25, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3329, some c3387, some c2881, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6257 : lratChecker f6257 p6257 = .success := by decide +kernel
theorem unsat6257 : Unsatisfiable (PosFin 65) f6257 := by
  apply lratCheckerSound f6257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6257
  · intro a ha; simp [p6257] at ha; subst a; trivial
  · exact checked6257
theorem derived6257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6257 := by
  apply localUnsat_implies_entails f6257 [c3329, c3387, c2881] c6257 unsat6257 (by rfl) a
  have h0 : Entails.eval a c3329 := h 3328 (by decide)
  have h1 : Entails.eval a c3387 := h 3386 (by decide)
  have h2 : Entails.eval a c2881 := h 2880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6258 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2805, some c2817, some c3362, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p6258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6258 : lratChecker f6258 p6258 = .success := by decide +kernel
theorem unsat6258 : Unsatisfiable (PosFin 65) f6258 := by
  apply lratCheckerSound f6258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6258
  · intro a ha; simp [p6258] at ha; subst a; trivial
  · exact checked6258
theorem derived6258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6258 := by
  apply localUnsat_implies_entails f6258 [c2805, c2817, c3362] c6258 unsat6258 (by rfl) a
  have h0 : Entails.eval a c2805 := h 2804 (by decide)
  have h1 : Entails.eval a c2817 := h 2816 (by decide)
  have h2 : Entails.eval a c3362 := h 3361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6259 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6250, some c6238, some c6253, some c4866, some c4483, some c5679, some c6252, some c6227, some c4121, some c3957, some c5332, some c5293, some c6241, some c4634, some c6239, some c6255, some c5063, some c5130, some c5056, some c5876, some c5232, some c6256, some c6258, some c6257, some c2790, some c2794, some c3362, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked6259 : lratChecker f6259 p6259 = .success := by decide +kernel
theorem unsat6259 : Unsatisfiable (PosFin 65) f6259 := by
  apply lratCheckerSound f6259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6259
  · intro a ha; simp [p6259] at ha; subst a; trivial
  · exact checked6259
theorem derived6259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6259 := by
  apply localUnsat_implies_entails f6259 [c6250, c6238, c6253, c4866, c4483, c5679, c6252, c6227, c4121, c3957, c5332, c5293, c6241, c4634, c6239, c6255, c5063, c5130, c5056, c5876, c5232, c6256, c6258, c6257, c2790, c2794, c3362] c6259 unsat6259 (by rfl) a
  have h0 : Entails.eval a c6250 := derived6250 a h
  have h1 : Entails.eval a c6238 := derived6238 a h
  have h2 : Entails.eval a c6253 := derived6253 a h
  have h3 : Entails.eval a c4866 := h 4865 (by decide)
  have h4 : Entails.eval a c4483 := h 4482 (by decide)
  have h5 : Entails.eval a c5679 := h 5678 (by decide)
  have h6 : Entails.eval a c6252 := derived6252 a h
  have h7 : Entails.eval a c6227 := derived6227 a h
  have h8 : Entails.eval a c4121 := h 4120 (by decide)
  have h9 : Entails.eval a c3957 := h 3956 (by decide)
  have h10 : Entails.eval a c5332 := h 5331 (by decide)
  have h11 : Entails.eval a c5293 := h 5292 (by decide)
  have h12 : Entails.eval a c6241 := derived6241 a h
  have h13 : Entails.eval a c4634 := h 4633 (by decide)
  have h14 : Entails.eval a c6239 := derived6239 a h
  have h15 : Entails.eval a c6255 := derived6255 a h
  have h16 : Entails.eval a c5063 := h 5062 (by decide)
  have h17 : Entails.eval a c5130 := h 5129 (by decide)
  have h18 : Entails.eval a c5056 := h 5055 (by decide)
  have h19 : Entails.eval a c5876 := h 5875 (by decide)
  have h20 : Entails.eval a c5232 := h 5231 (by decide)
  have h21 : Entails.eval a c6256 := derived6256 a h
  have h22 : Entails.eval a c6258 := derived6258 a h
  have h23 : Entails.eval a c6257 := derived6257 a h
  have h24 : Entails.eval a c2790 := h 2789 (by decide)
  have h25 : Entails.eval a c2794 := h 2793 (by decide)
  have h26 : Entails.eval a c3362 := h 3361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6260 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6227, some c6250, some c6252, some c6253, some c6259, some c5017, some c4652, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6260 : lratChecker f6260 p6260 = .success := by decide +kernel
theorem unsat6260 : Unsatisfiable (PosFin 65) f6260 := by
  apply lratCheckerSound f6260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6260
  · intro a ha; simp [p6260] at ha; subst a; trivial
  · exact checked6260
theorem derived6260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6260 := by
  apply localUnsat_implies_entails f6260 [c6238, c6227, c6250, c6252, c6253, c6259, c5017, c4652] c6260 unsat6260 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6250 := derived6250 a h
  have h3 : Entails.eval a c6252 := derived6252 a h
  have h4 : Entails.eval a c6253 := derived6253 a h
  have h5 : Entails.eval a c6259 := derived6259 a h
  have h6 : Entails.eval a c5017 := h 5016 (by decide)
  have h7 : Entails.eval a c4652 := h 4651 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6261 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨41, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4698, some c4842, some c5307, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6261 : lratChecker f6261 p6261 = .success := by decide +kernel
theorem unsat6261 : Unsatisfiable (PosFin 65) f6261 := by
  apply lratCheckerSound f6261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6261
  · intro a ha; simp [p6261] at ha; subst a; trivial
  · exact checked6261
theorem derived6261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6261 := by
  apply localUnsat_implies_entails f6261 [c4698, c4842, c5307] c6261 unsat6261 (by rfl) a
  have h0 : Entails.eval a c4698 := h 4697 (by decide)
  have h1 : Entails.eval a c4842 := h 4841 (by decide)
  have h2 : Entails.eval a c5307 := h 5306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6262 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6227, some c6260, some c6261, some c4696, some c4837, some c5303, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6262 : lratChecker f6262 p6262 = .success := by decide +kernel
theorem unsat6262 : Unsatisfiable (PosFin 65) f6262 := by
  apply lratCheckerSound f6262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6262
  · intro a ha; simp [p6262] at ha; subst a; trivial
  · exact checked6262
theorem derived6262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6262 := by
  apply localUnsat_implies_entails f6262 [c6238, c6227, c6260, c6261, c4696, c4837, c5303] c6262 unsat6262 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6260 := derived6260 a h
  have h3 : Entails.eval a c6261 := derived6261 a h
  have h4 : Entails.eval a c4696 := h 4695 (by decide)
  have h5 : Entails.eval a c4837 := h 4836 (by decide)
  have h6 : Entails.eval a c5303 := h 5302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6263 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5310, some c5308, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6263 : lratChecker f6263 p6263 = .success := by decide +kernel
theorem unsat6263 : Unsatisfiable (PosFin 65) f6263 := by
  apply lratCheckerSound f6263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6263
  · intro a ha; simp [p6263] at ha; subst a; trivial
  · exact checked6263
theorem derived6263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6263 := by
  apply localUnsat_implies_entails f6263 [c6227, c5310, c5308] c6263 unsat6263 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5310 := h 5309 (by decide)
  have h2 : Entails.eval a c5308 := h 5307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6264 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨53, by decide⟩, true), (⟨41, by decide⟩, true), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4843, some c4845, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6264 : lratChecker f6264 p6264 = .success := by decide +kernel
theorem unsat6264 : Unsatisfiable (PosFin 65) f6264 := by
  apply lratCheckerSound f6264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6264
  · intro a ha; simp [p6264] at ha; subst a; trivial
  · exact checked6264
theorem derived6264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6264 := by
  apply localUnsat_implies_entails f6264 [c6227, c4843, c4845] c6264 unsat6264 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4843 := h 4842 (by decide)
  have h2 : Entails.eval a c4845 := h 4844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6265 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6261, some c6264, some c6263, some c4700, some c4699, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6265 : lratChecker f6265 p6265 = .success := by decide +kernel
theorem unsat6265 : Unsatisfiable (PosFin 65) f6265 := by
  apply lratCheckerSound f6265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6265
  · intro a ha; simp [p6265] at ha; subst a; trivial
  · exact checked6265
theorem derived6265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6265 := by
  apply localUnsat_implies_entails f6265 [c6227, c6261, c6264, c6263, c4700, c4699] c6265 unsat6265 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6261 := derived6261 a h
  have h2 : Entails.eval a c6264 := derived6264 a h
  have h3 : Entails.eval a c6263 := derived6263 a h
  have h4 : Entails.eval a c4700 := h 4699 (by decide)
  have h5 : Entails.eval a c4699 := h 4698 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6266 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨44, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5680, some c4719, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6266 : lratChecker f6266 p6266 = .success := by decide +kernel
theorem unsat6266 : Unsatisfiable (PosFin 65) f6266 := by
  apply lratCheckerSound f6266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6266
  · intro a ha; simp [p6266] at ha; subst a; trivial
  · exact checked6266
theorem derived6266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6266 := by
  apply localUnsat_implies_entails f6266 [c5680, c4719] c6266 unsat6266 (by rfl) a
  have h0 : Entails.eval a c5680 := h 5679 (by decide)
  have h1 : Entails.eval a c4719 := h 4718 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6267 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6266, some c5696, some c3641, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6267 : lratChecker f6267 p6267 = .success := by decide +kernel
theorem unsat6267 : Unsatisfiable (PosFin 65) f6267 := by
  apply lratCheckerSound f6267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6267
  · intro a ha; simp [p6267] at ha; subst a; trivial
  · exact checked6267
theorem derived6267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6267 := by
  apply localUnsat_implies_entails f6267 [c6227, c6266, c5696, c3641] c6267 unsat6267 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6266 := derived6266 a h
  have h2 : Entails.eval a c5696 := h 5695 (by decide)
  have h3 : Entails.eval a c3641 := h 3640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6268 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨44, by decide⟩, true), (⟨51, by decide⟩, false), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5005, some c4683, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6268 : lratChecker f6268 p6268 = .success := by decide +kernel
theorem unsat6268 : Unsatisfiable (PosFin 65) f6268 := by
  apply lratCheckerSound f6268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6268
  · intro a ha; simp [p6268] at ha; subst a; trivial
  · exact checked6268
theorem derived6268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6268 := by
  apply localUnsat_implies_entails f6268 [c5005, c4683] c6268 unsat6268 (by rfl) a
  have h0 : Entails.eval a c5005 := h 5004 (by decide)
  have h1 : Entails.eval a c4683 := h 4682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6269 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6262, some c6238, some c6265, some c6227, some c6267, some c6268, some c4119, some c4719, some c3959, some c4484, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6269 : lratChecker f6269 p6269 = .success := by decide +kernel
theorem unsat6269 : Unsatisfiable (PosFin 65) f6269 := by
  apply lratCheckerSound f6269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6269
  · intro a ha; simp [p6269] at ha; subst a; trivial
  · exact checked6269
theorem derived6269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6269 := by
  apply localUnsat_implies_entails f6269 [c6262, c6238, c6265, c6227, c6267, c6268, c4119, c4719, c3959, c4484] c6269 unsat6269 (by rfl) a
  have h0 : Entails.eval a c6262 := derived6262 a h
  have h1 : Entails.eval a c6238 := derived6238 a h
  have h2 : Entails.eval a c6265 := derived6265 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6267 := derived6267 a h
  have h5 : Entails.eval a c6268 := derived6268 a h
  have h6 : Entails.eval a c4119 := h 4118 (by decide)
  have h7 : Entails.eval a c4719 := h 4718 (by decide)
  have h8 : Entails.eval a c3959 := h 3958 (by decide)
  have h9 : Entails.eval a c4484 := h 4483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6270 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨58, by decide⟩, true), (⟨44, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c3949, some c4050, some c5221, some c4389, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6270 : lratChecker f6270 p6270 = .success := by decide +kernel
theorem unsat6270 : Unsatisfiable (PosFin 65) f6270 := by
  apply lratCheckerSound f6270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6270
  · intro a ha; simp [p6270] at ha; subst a; trivial
  · exact checked6270
theorem derived6270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6270 := by
  apply localUnsat_implies_entails f6270 [c6227, c3949, c4050, c5221, c4389] c6270 unsat6270 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c3949 := h 3948 (by decide)
  have h2 : Entails.eval a c4050 := h 4049 (by decide)
  have h3 : Entails.eval a c5221 := h 5220 (by decide)
  have h4 : Entails.eval a c4389 := h 4388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6271 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6262, some c6238, some c6265, some c6227, some c6269, some c6263, some c6268, some c4119, some c5333, some c4331, some c4269, some c4612, some c6270, some c5116, some c5006, some c5008, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6271 : lratChecker f6271 p6271 = .success := by decide +kernel
theorem unsat6271 : Unsatisfiable (PosFin 65) f6271 := by
  apply lratCheckerSound f6271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6271
  · intro a ha; simp [p6271] at ha; subst a; trivial
  · exact checked6271
theorem derived6271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6271 := by
  apply localUnsat_implies_entails f6271 [c6262, c6238, c6265, c6227, c6269, c6263, c6268, c4119, c5333, c4331, c4269, c4612, c6270, c5116, c5006, c5008] c6271 unsat6271 (by rfl) a
  have h0 : Entails.eval a c6262 := derived6262 a h
  have h1 : Entails.eval a c6238 := derived6238 a h
  have h2 : Entails.eval a c6265 := derived6265 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6269 := derived6269 a h
  have h5 : Entails.eval a c6263 := derived6263 a h
  have h6 : Entails.eval a c6268 := derived6268 a h
  have h7 : Entails.eval a c4119 := h 4118 (by decide)
  have h8 : Entails.eval a c5333 := h 5332 (by decide)
  have h9 : Entails.eval a c4331 := h 4330 (by decide)
  have h10 : Entails.eval a c4269 := h 4268 (by decide)
  have h11 : Entails.eval a c4612 := h 4611 (by decide)
  have h12 : Entails.eval a c6270 := derived6270 a h
  have h13 : Entails.eval a c5116 := h 5115 (by decide)
  have h14 : Entails.eval a c5006 := h 5005 (by decide)
  have h15 : Entails.eval a c5008 := h 5007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6272 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨43, by decide⟩, false), (⟨58, by decide⟩, true), (⟨51, by decide⟩, false), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5116, some c5006, some c5008, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6272 : lratChecker f6272 p6272 = .success := by decide +kernel
theorem unsat6272 : Unsatisfiable (PosFin 65) f6272 := by
  apply lratCheckerSound f6272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6272
  · intro a ha; simp [p6272] at ha; subst a; trivial
  · exact checked6272
theorem derived6272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6272 := by
  apply localUnsat_implies_entails f6272 [c5116, c5006, c5008] c6272 unsat6272 (by rfl) a
  have h0 : Entails.eval a c5116 := h 5115 (by decide)
  have h1 : Entails.eval a c5006 := h 5005 (by decide)
  have h2 : Entails.eval a c5008 := h 5007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6273 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6265, some c6262, some c6271, some c5307, some c6268, some c5332, some c6227, some c4483, some c6272, some c3601, some c5214, some c5221, some c4389, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6273 : lratChecker f6273 p6273 = .success := by decide +kernel
theorem unsat6273 : Unsatisfiable (PosFin 65) f6273 := by
  apply lratCheckerSound f6273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6273
  · intro a ha; simp [p6273] at ha; subst a; trivial
  · exact checked6273
theorem derived6273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6273 := by
  apply localUnsat_implies_entails f6273 [c6238, c6265, c6262, c6271, c5307, c6268, c5332, c6227, c4483, c6272, c3601, c5214, c5221, c4389] c6273 unsat6273 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6265 := derived6265 a h
  have h2 : Entails.eval a c6262 := derived6262 a h
  have h3 : Entails.eval a c6271 := derived6271 a h
  have h4 : Entails.eval a c5307 := h 5306 (by decide)
  have h5 : Entails.eval a c6268 := derived6268 a h
  have h6 : Entails.eval a c5332 := h 5331 (by decide)
  have h7 : Entails.eval a c6227 := derived6227 a h
  have h8 : Entails.eval a c4483 := h 4482 (by decide)
  have h9 : Entails.eval a c6272 := derived6272 a h
  have h10 : Entails.eval a c3601 := h 3600 (by decide)
  have h11 : Entails.eval a c5214 := h 5213 (by decide)
  have h12 : Entails.eval a c5221 := h 5220 (by decide)
  have h13 : Entails.eval a c4389 := h 4388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6274 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6271, some c6262, some c6238, some c6265, some c6227, some c5332, some c5307, some c6268, some c6273, some c4866, some c4266, some c5474, some c4128, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6274 : lratChecker f6274 p6274 = .success := by decide +kernel
theorem unsat6274 : Unsatisfiable (PosFin 65) f6274 := by
  apply lratCheckerSound f6274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6274
  · intro a ha; simp [p6274] at ha; subst a; trivial
  · exact checked6274
theorem derived6274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6274 := by
  apply localUnsat_implies_entails f6274 [c6271, c6262, c6238, c6265, c6227, c5332, c5307, c6268, c6273, c4866, c4266, c5474, c4128] c6274 unsat6274 (by rfl) a
  have h0 : Entails.eval a c6271 := derived6271 a h
  have h1 : Entails.eval a c6262 := derived6262 a h
  have h2 : Entails.eval a c6238 := derived6238 a h
  have h3 : Entails.eval a c6265 := derived6265 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c5332 := h 5331 (by decide)
  have h6 : Entails.eval a c5307 := h 5306 (by decide)
  have h7 : Entails.eval a c6268 := derived6268 a h
  have h8 : Entails.eval a c6273 := derived6273 a h
  have h9 : Entails.eval a c4866 := h 4865 (by decide)
  have h10 : Entails.eval a c4266 := h 4265 (by decide)
  have h11 : Entails.eval a c5474 := h 5473 (by decide)
  have h12 : Entails.eval a c4128 := h 4127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6275 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6265, some c6271, some c6274, some c3647, some c4718, some c4220, some c4483, some c3957, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6275 : lratChecker f6275 p6275 = .success := by decide +kernel
theorem unsat6275 : Unsatisfiable (PosFin 65) f6275 := by
  apply lratCheckerSound f6275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6275
  · intro a ha; simp [p6275] at ha; subst a; trivial
  · exact checked6275
theorem derived6275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6275 := by
  apply localUnsat_implies_entails f6275 [c6238, c6265, c6271, c6274, c3647, c4718, c4220, c4483, c3957] c6275 unsat6275 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6265 := derived6265 a h
  have h2 : Entails.eval a c6271 := derived6271 a h
  have h3 : Entails.eval a c6274 := derived6274 a h
  have h4 : Entails.eval a c3647 := h 3646 (by decide)
  have h5 : Entails.eval a c4718 := h 4717 (by decide)
  have h6 : Entails.eval a c4220 := h 4219 (by decide)
  have h7 : Entails.eval a c4483 := h 4482 (by decide)
  have h8 : Entails.eval a c3957 := h 3956 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6276 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c5679, some c4483, some c6251, some c4777, some c4455, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6276 : lratChecker f6276 p6276 = .success := by decide +kernel
theorem unsat6276 : Unsatisfiable (PosFin 65) f6276 := by
  apply lratCheckerSound f6276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6276
  · intro a ha; simp [p6276] at ha; subst a; trivial
  · exact checked6276
theorem derived6276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6276 := by
  apply localUnsat_implies_entails f6276 [c6227, c5679, c4483, c6251, c4777, c4455] c6276 unsat6276 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c5679 := h 5678 (by decide)
  have h2 : Entails.eval a c4483 := h 4482 (by decide)
  have h3 : Entails.eval a c6251 := derived6251 a h
  have h4 : Entails.eval a c4777 := h 4776 (by decide)
  have h5 : Entails.eval a c4455 := h 4454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6277 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6238, some c6275, some c6276, some c6227, some c5675, some c6263, some c6267, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6277 : lratChecker f6277 p6277 = .success := by decide +kernel
theorem unsat6277 : Unsatisfiable (PosFin 65) f6277 := by
  apply lratCheckerSound f6277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6277
  · intro a ha; simp [p6277] at ha; subst a; trivial
  · exact checked6277
theorem derived6277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6277 := by
  apply localUnsat_implies_entails f6277 [c6238, c6275, c6276, c6227, c5675, c6263, c6267] c6277 unsat6277 (by rfl) a
  have h0 : Entails.eval a c6238 := derived6238 a h
  have h1 : Entails.eval a c6275 := derived6275 a h
  have h2 : Entails.eval a c6276 := derived6276 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c5675 := h 5674 (by decide)
  have h5 : Entails.eval a c6263 := derived6263 a h
  have h6 : Entails.eval a c6267 := derived6267 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6278 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6275, some c6238, some c6227, some c6276, some c6277, some c4774, some c4776, some c4775, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6278 : lratChecker f6278 p6278 = .success := by decide +kernel
theorem unsat6278 : Unsatisfiable (PosFin 65) f6278 := by
  apply lratCheckerSound f6278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6278
  · intro a ha; simp [p6278] at ha; subst a; trivial
  · exact checked6278
theorem derived6278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6278 := by
  apply localUnsat_implies_entails f6278 [c6275, c6238, c6227, c6276, c6277, c4774, c4776, c4775] c6278 unsat6278 (by rfl) a
  have h0 : Entails.eval a c6275 := derived6275 a h
  have h1 : Entails.eval a c6238 := derived6238 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6276 := derived6276 a h
  have h4 : Entails.eval a c6277 := derived6277 a h
  have h5 : Entails.eval a c4774 := h 4773 (by decide)
  have h6 : Entails.eval a c4776 := h 4775 (by decide)
  have h7 : Entails.eval a c4775 := h 4774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6279 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c4757, some c4763, some c4761, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6279 : lratChecker f6279 p6279 = .success := by decide +kernel
theorem unsat6279 : Unsatisfiable (PosFin 65) f6279 := by
  apply lratCheckerSound f6279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6279
  · intro a ha; simp [p6279] at ha; subst a; trivial
  · exact checked6279
theorem derived6279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6279 := by
  apply localUnsat_implies_entails f6279 [c6227, c4757, c4763, c4761] c6279 unsat6279 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c4757 := h 4756 (by decide)
  have h2 : Entails.eval a c4763 := h 4762 (by decide)
  have h3 : Entails.eval a c4761 := h 4760 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6280 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6275, some c6278, some c6279, some c4764, some c4866, some c4718, some c4762, some c4772, some c5366, some c4775, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6280 : lratChecker f6280 p6280 = .success := by decide +kernel
theorem unsat6280 : Unsatisfiable (PosFin 65) f6280 := by
  apply lratCheckerSound f6280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6280
  · intro a ha; simp [p6280] at ha; subst a; trivial
  · exact checked6280
theorem derived6280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6280 := by
  apply localUnsat_implies_entails f6280 [c6227, c6275, c6278, c6279, c4764, c4866, c4718, c4762, c4772, c5366, c4775] c6280 unsat6280 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6275 := derived6275 a h
  have h2 : Entails.eval a c6278 := derived6278 a h
  have h3 : Entails.eval a c6279 := derived6279 a h
  have h4 : Entails.eval a c4764 := h 4763 (by decide)
  have h5 : Entails.eval a c4866 := h 4865 (by decide)
  have h6 : Entails.eval a c4718 := h 4717 (by decide)
  have h7 : Entails.eval a c4762 := h 4761 (by decide)
  have h8 : Entails.eval a c4772 := h 4771 (by decide)
  have h9 : Entails.eval a c5366 := h 5365 (by decide)
  have h10 : Entails.eval a c4775 := h 4774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived6280

end CochromaticTwenty.Certificates.FixedCore1
