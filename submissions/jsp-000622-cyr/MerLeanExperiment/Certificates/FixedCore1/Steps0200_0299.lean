import MerLeanExperiment.Certificates.FixedCore1.Steps0100_0199

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6081 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨58, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, true), (⟨37, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6037, some c4831, some c5793, some c5129, some c5617, some c4006, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6081 : lratChecker f6081 p6081 = .success := by decide +kernel
theorem unsat6081 : Unsatisfiable (PosFin 65) f6081 := by
  apply lratCheckerSound f6081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6081
  · intro a ha; simp [p6081] at ha; subst a; trivial
  · exact checked6081
theorem derived6081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6081 := by
  apply localUnsat_implies_entails f6081 [c6037, c4831, c5793, c5129, c5617, c4006] c6081 unsat6081 (by rfl) a
  have h0 : Entails.eval a c6037 := derived6037 a h
  have h1 : Entails.eval a c4831 := h 4830 (by decide)
  have h2 : Entails.eval a c5793 := h 5792 (by decide)
  have h3 : Entails.eval a c5129 := h 5128 (by decide)
  have h4 : Entails.eval a c5617 := h 5616 (by decide)
  have h5 : Entails.eval a c4006 := h 4005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6082 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3652, some c6079, some c6037, some c6080, some c4974, some c4964, some c4971, some c3754, some c5957, some c4146, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6082 : lratChecker f6082 p6082 = .success := by decide +kernel
theorem unsat6082 : Unsatisfiable (PosFin 65) f6082 := by
  apply lratCheckerSound f6082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6082
  · intro a ha; simp [p6082] at ha; subst a; trivial
  · exact checked6082
theorem derived6082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6082 := by
  apply localUnsat_implies_entails f6082 [c3652, c6079, c6037, c6080, c4974, c4964, c4971, c3754, c5957, c4146] c6082 unsat6082 (by rfl) a
  have h0 : Entails.eval a c3652 := h 3651 (by decide)
  have h1 : Entails.eval a c6079 := derived6079 a h
  have h2 : Entails.eval a c6037 := derived6037 a h
  have h3 : Entails.eval a c6080 := derived6080 a h
  have h4 : Entails.eval a c4974 := h 4973 (by decide)
  have h5 : Entails.eval a c4964 := h 4963 (by decide)
  have h6 : Entails.eval a c4971 := h 4970 (by decide)
  have h7 : Entails.eval a c3754 := h 3753 (by decide)
  have h8 : Entails.eval a c5957 := derived5957 a h
  have h9 : Entails.eval a c4146 := h 4145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6083 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, false), (⟨45, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3708, some c4967, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6083 : lratChecker f6083 p6083 = .success := by decide +kernel
theorem unsat6083 : Unsatisfiable (PosFin 65) f6083 := by
  apply lratCheckerSound f6083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6083
  · intro a ha; simp [p6083] at ha; subst a; trivial
  · exact checked6083
theorem derived6083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6083 := by
  apply localUnsat_implies_entails f6083 [c3708, c4967] c6083 unsat6083 (by rfl) a
  have h0 : Entails.eval a c3708 := h 3707 (by decide)
  have h1 : Entails.eval a c4967 := h 4966 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6084 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6079, some c6037, some c3652, some c6083, some c6080, some c6082, some c4974, some c4170, some c4964, some c5390, some c5368, some c4273, some c6005, some c3925, some c5192, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6084 : lratChecker f6084 p6084 = .success := by decide +kernel
theorem unsat6084 : Unsatisfiable (PosFin 65) f6084 := by
  apply lratCheckerSound f6084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6084
  · intro a ha; simp [p6084] at ha; subst a; trivial
  · exact checked6084
theorem derived6084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6084 := by
  apply localUnsat_implies_entails f6084 [c6079, c6037, c3652, c6083, c6080, c6082, c4974, c4170, c4964, c5390, c5368, c4273, c6005, c3925, c5192] c6084 unsat6084 (by rfl) a
  have h0 : Entails.eval a c6079 := derived6079 a h
  have h1 : Entails.eval a c6037 := derived6037 a h
  have h2 : Entails.eval a c3652 := h 3651 (by decide)
  have h3 : Entails.eval a c6083 := derived6083 a h
  have h4 : Entails.eval a c6080 := derived6080 a h
  have h5 : Entails.eval a c6082 := derived6082 a h
  have h6 : Entails.eval a c4974 := h 4973 (by decide)
  have h7 : Entails.eval a c4170 := h 4169 (by decide)
  have h8 : Entails.eval a c4964 := h 4963 (by decide)
  have h9 : Entails.eval a c5390 := h 5389 (by decide)
  have h10 : Entails.eval a c5368 := h 5367 (by decide)
  have h11 : Entails.eval a c4273 := h 4272 (by decide)
  have h12 : Entails.eval a c6005 := derived6005 a h
  have h13 : Entails.eval a c3925 := h 3924 (by decide)
  have h14 : Entails.eval a c5192 := h 5191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6085 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6079, some c6084, some c5103, some c5152, some c4807, some c3988, some c4170, some c4888, some c5368, some c4974, some c6015, some c6005, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6085 : lratChecker f6085 p6085 = .success := by decide +kernel
theorem unsat6085 : Unsatisfiable (PosFin 65) f6085 := by
  apply lratCheckerSound f6085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6085
  · intro a ha; simp [p6085] at ha; subst a; trivial
  · exact checked6085
theorem derived6085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6085 := by
  apply localUnsat_implies_entails f6085 [c6079, c6084, c5103, c5152, c4807, c3988, c4170, c4888, c5368, c4974, c6015, c6005] c6085 unsat6085 (by rfl) a
  have h0 : Entails.eval a c6079 := derived6079 a h
  have h1 : Entails.eval a c6084 := derived6084 a h
  have h2 : Entails.eval a c5103 := h 5102 (by decide)
  have h3 : Entails.eval a c5152 := h 5151 (by decide)
  have h4 : Entails.eval a c4807 := h 4806 (by decide)
  have h5 : Entails.eval a c3988 := h 3987 (by decide)
  have h6 : Entails.eval a c4170 := h 4169 (by decide)
  have h7 : Entails.eval a c4888 := h 4887 (by decide)
  have h8 : Entails.eval a c5368 := h 5367 (by decide)
  have h9 : Entails.eval a c4974 := h 4973 (by decide)
  have h10 : Entails.eval a c6015 := derived6015 a h
  have h11 : Entails.eval a c6005 := derived6005 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6086 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨59, by decide⟩, true), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨34, by decide⟩, true), (⟨46, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4589, some c4333, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6086 : lratChecker f6086 p6086 = .success := by decide +kernel
theorem unsat6086 : Unsatisfiable (PosFin 65) f6086 := by
  apply lratCheckerSound f6086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6086
  · intro a ha; simp [p6086] at ha; subst a; trivial
  · exact checked6086
theorem derived6086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6086 := by
  apply localUnsat_implies_entails f6086 [c4589, c4333] c6086 unsat6086 (by rfl) a
  have h0 : Entails.eval a c4589 := h 4588 (by decide)
  have h1 : Entails.eval a c4333 := h 4332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6087 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5251, some c4199, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6087 : lratChecker f6087 p6087 = .success := by decide +kernel
theorem unsat6087 : Unsatisfiable (PosFin 65) f6087 := by
  apply lratCheckerSound f6087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6087
  · intro a ha; simp [p6087] at ha; subst a; trivial
  · exact checked6087
theorem derived6087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6087 := by
  apply localUnsat_implies_entails f6087 [c5251, c4199] c6087 unsat6087 (by rfl) a
  have h0 : Entails.eval a c5251 := h 5250 (by decide)
  have h1 : Entails.eval a c4199 := h 4198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6088 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨59, by decide⟩, false), (⟨57, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5904, some c5632, some c3781, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6088 : lratChecker f6088 p6088 = .success := by decide +kernel
theorem unsat6088 : Unsatisfiable (PosFin 65) f6088 := by
  apply lratCheckerSound f6088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6088
  · intro a ha; simp [p6088] at ha; subst a; trivial
  · exact checked6088
theorem derived6088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6088 := by
  apply localUnsat_implies_entails f6088 [c5904, c5632, c3781] c6088 unsat6088 (by rfl) a
  have h0 : Entails.eval a c5904 := derived5904 a h
  have h1 : Entails.eval a c5632 := h 5631 (by decide)
  have h2 : Entails.eval a c3781 := h 3780 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6089 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨52, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6079, some c6084, some c5103, some c5152, some c4807, some c3988, some c6087, some c4170, some c4888, some c4273, some c6066, some c6085, some c4422, some c5957, some c6086, some c6088, some c5048, some c4583, some c4610, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked6089 : lratChecker f6089 p6089 = .success := by decide +kernel
theorem unsat6089 : Unsatisfiable (PosFin 65) f6089 := by
  apply lratCheckerSound f6089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6089
  · intro a ha; simp [p6089] at ha; subst a; trivial
  · exact checked6089
theorem derived6089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6089 := by
  apply localUnsat_implies_entails f6089 [c6079, c6084, c5103, c5152, c4807, c3988, c6087, c4170, c4888, c4273, c6066, c6085, c4422, c5957, c6086, c6088, c5048, c4583, c4610] c6089 unsat6089 (by rfl) a
  have h0 : Entails.eval a c6079 := derived6079 a h
  have h1 : Entails.eval a c6084 := derived6084 a h
  have h2 : Entails.eval a c5103 := h 5102 (by decide)
  have h3 : Entails.eval a c5152 := h 5151 (by decide)
  have h4 : Entails.eval a c4807 := h 4806 (by decide)
  have h5 : Entails.eval a c3988 := h 3987 (by decide)
  have h6 : Entails.eval a c6087 := derived6087 a h
  have h7 : Entails.eval a c4170 := h 4169 (by decide)
  have h8 : Entails.eval a c4888 := h 4887 (by decide)
  have h9 : Entails.eval a c4273 := h 4272 (by decide)
  have h10 : Entails.eval a c6066 := derived6066 a h
  have h11 : Entails.eval a c6085 := derived6085 a h
  have h12 : Entails.eval a c4422 := h 4421 (by decide)
  have h13 : Entails.eval a c5957 := derived5957 a h
  have h14 : Entails.eval a c6086 := derived6086 a h
  have h15 : Entails.eval a c6088 := derived6088 a h
  have h16 : Entails.eval a c5048 := h 5047 (by decide)
  have h17 : Entails.eval a c4583 := h 4582 (by decide)
  have h18 : Entails.eval a c4610 := h 4609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6090 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3695, some c3700, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6090 : lratChecker f6090 p6090 = .success := by decide +kernel
theorem unsat6090 : Unsatisfiable (PosFin 65) f6090 := by
  apply lratCheckerSound f6090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6090
  · intro a ha; simp [p6090] at ha; subst a; trivial
  · exact checked6090
theorem derived6090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6090 := by
  apply localUnsat_implies_entails f6090 [c3695, c3700] c6090 unsat6090 (by rfl) a
  have h0 : Entails.eval a c3695 := h 3694 (by decide)
  have h1 : Entails.eval a c3700 := h 3699 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6091 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6066, some c6079, some c6084, some c5103, some c5152, some c4807, some c3988, some c6087, some c6090, some c6089, some c3778, some c5245, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6091 : lratChecker f6091 p6091 = .success := by decide +kernel
theorem unsat6091 : Unsatisfiable (PosFin 65) f6091 := by
  apply lratCheckerSound f6091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6091
  · intro a ha; simp [p6091] at ha; subst a; trivial
  · exact checked6091
theorem derived6091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6091 := by
  apply localUnsat_implies_entails f6091 [c6066, c6079, c6084, c5103, c5152, c4807, c3988, c6087, c6090, c6089, c3778, c5245] c6091 unsat6091 (by rfl) a
  have h0 : Entails.eval a c6066 := derived6066 a h
  have h1 : Entails.eval a c6079 := derived6079 a h
  have h2 : Entails.eval a c6084 := derived6084 a h
  have h3 : Entails.eval a c5103 := h 5102 (by decide)
  have h4 : Entails.eval a c5152 := h 5151 (by decide)
  have h5 : Entails.eval a c4807 := h 4806 (by decide)
  have h6 : Entails.eval a c3988 := h 3987 (by decide)
  have h7 : Entails.eval a c6087 := derived6087 a h
  have h8 : Entails.eval a c6090 := derived6090 a h
  have h9 : Entails.eval a c6089 := derived6089 a h
  have h10 : Entails.eval a c3778 := h 3777 (by decide)
  have h11 : Entails.eval a c5245 := h 5244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6092 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3818, some c3550, some c3860, some c4528, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6092 : lratChecker f6092 p6092 = .success := by decide +kernel
theorem unsat6092 : Unsatisfiable (PosFin 65) f6092 := by
  apply lratCheckerSound f6092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6092
  · intro a ha; simp [p6092] at ha; subst a; trivial
  · exact checked6092
theorem derived6092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6092 := by
  apply localUnsat_implies_entails f6092 [c3818, c3550, c3860, c4528] c6092 unsat6092 (by rfl) a
  have h0 : Entails.eval a c3818 := h 3817 (by decide)
  have h1 : Entails.eval a c3550 := h 3549 (by decide)
  have h2 : Entails.eval a c3860 := h 3859 (by decide)
  have h3 : Entails.eval a c4528 := h 4527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6093 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6092, some c4170, some c4831, some c3446, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6093 : lratChecker f6093 p6093 = .success := by decide +kernel
theorem unsat6093 : Unsatisfiable (PosFin 65) f6093 := by
  apply lratCheckerSound f6093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6093
  · intro a ha; simp [p6093] at ha; subst a; trivial
  · exact checked6093
theorem derived6093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6093 := by
  apply localUnsat_implies_entails f6093 [c6092, c4170, c4831, c3446] c6093 unsat6093 (by rfl) a
  have h0 : Entails.eval a c6092 := derived6092 a h
  have h1 : Entails.eval a c4170 := h 4169 (by decide)
  have h2 : Entails.eval a c4831 := h 4830 (by decide)
  have h3 : Entails.eval a c3446 := h 3445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6094 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨64, by decide⟩, false), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5103, some c6037, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6094 : lratChecker f6094 p6094 = .success := by decide +kernel
theorem unsat6094 : Unsatisfiable (PosFin 65) f6094 := by
  apply lratCheckerSound f6094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6094
  · intro a ha; simp [p6094] at ha; subst a; trivial
  · exact checked6094
theorem derived6094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6094 := by
  apply localUnsat_implies_entails f6094 [c5103, c6037] c6094 unsat6094 (by rfl) a
  have h0 : Entails.eval a c5103 := h 5102 (by decide)
  have h1 : Entails.eval a c6037 := derived6037 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6095 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6092, some c6093, some c6094, some c6043, some c4031, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6095 : lratChecker f6095 p6095 = .success := by decide +kernel
theorem unsat6095 : Unsatisfiable (PosFin 65) f6095 := by
  apply lratCheckerSound f6095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6095
  · intro a ha; simp [p6095] at ha; subst a; trivial
  · exact checked6095
theorem derived6095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6095 := by
  apply localUnsat_implies_entails f6095 [c6092, c6093, c6094, c6043, c4031] c6095 unsat6095 (by rfl) a
  have h0 : Entails.eval a c6092 := derived6092 a h
  have h1 : Entails.eval a c6093 := derived6093 a h
  have h2 : Entails.eval a c6094 := derived6094 a h
  have h3 : Entails.eval a c6043 := derived6043 a h
  have h4 : Entails.eval a c4031 := h 4030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6096 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨64, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6091, some c6095, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6096 : lratChecker f6096 p6096 = .success := by decide +kernel
theorem unsat6096 : Unsatisfiable (PosFin 65) f6096 := by
  apply lratCheckerSound f6096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6096
  · intro a ha; simp [p6096] at ha; subst a; trivial
  · exact checked6096
theorem derived6096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6096 := by
  apply localUnsat_implies_entails f6096 [c6091, c6095] c6096 unsat6096 (by rfl) a
  have h0 : Entails.eval a c6091 := derived6091 a h
  have h1 : Entails.eval a c6095 := derived6095 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6097 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6096, some c6066, some c4029, some c4037, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6097 : lratChecker f6097 p6097 = .success := by decide +kernel
theorem unsat6097 : Unsatisfiable (PosFin 65) f6097 := by
  apply lratCheckerSound f6097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6097
  · intro a ha; simp [p6097] at ha; subst a; trivial
  · exact checked6097
theorem derived6097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6097 := by
  apply localUnsat_implies_entails f6097 [c6096, c6066, c4029, c4037] c6097 unsat6097 (by rfl) a
  have h0 : Entails.eval a c6096 := derived6096 a h
  have h1 : Entails.eval a c6066 := derived6066 a h
  have h2 : Entails.eval a c4029 := h 4028 (by decide)
  have h3 : Entails.eval a c4037 := h 4036 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6098 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3453, some c4663, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6098 : lratChecker f6098 p6098 = .success := by decide +kernel
theorem unsat6098 : Unsatisfiable (PosFin 65) f6098 := by
  apply lratCheckerSound f6098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6098
  · intro a ha; simp [p6098] at ha; subst a; trivial
  · exact checked6098
theorem derived6098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6098 := by
  apply localUnsat_implies_entails f6098 [c3453, c4663] c6098 unsat6098 (by rfl) a
  have h0 : Entails.eval a c3453 := h 3452 (by decide)
  have h1 : Entails.eval a c4663 := h 4662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6099 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6096, some c6066, some c6097, some c6098, some c4656, some c3443, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6099 : lratChecker f6099 p6099 = .success := by decide +kernel
theorem unsat6099 : Unsatisfiable (PosFin 65) f6099 := by
  apply lratCheckerSound f6099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6099
  · intro a ha; simp [p6099] at ha; subst a; trivial
  · exact checked6099
theorem derived6099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6099 := by
  apply localUnsat_implies_entails f6099 [c6096, c6066, c6097, c6098, c4656, c3443] c6099 unsat6099 (by rfl) a
  have h0 : Entails.eval a c6096 := derived6096 a h
  have h1 : Entails.eval a c6066 := derived6066 a h
  have h2 : Entails.eval a c6097 := derived6097 a h
  have h3 : Entails.eval a c6098 := derived6098 a h
  have h4 : Entails.eval a c4656 := h 4655 (by decide)
  have h5 : Entails.eval a c3443 := h 3442 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6100 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3443, some c3499, some c4684, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6100 : lratChecker f6100 p6100 = .success := by decide +kernel
theorem unsat6100 : Unsatisfiable (PosFin 65) f6100 := by
  apply lratCheckerSound f6100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6100
  · intro a ha; simp [p6100] at ha; subst a; trivial
  · exact checked6100
theorem derived6100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6100 := by
  apply localUnsat_implies_entails f6100 [c3443, c3499, c4684] c6100 unsat6100 (by rfl) a
  have h0 : Entails.eval a c3443 := h 3442 (by decide)
  have h1 : Entails.eval a c3499 := h 3498 (by decide)
  have h2 : Entails.eval a c4684 := h 4683 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6101 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6099, some c6096, some c6066, some c6100, some c3557, some c3505, some c4398, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6101 : lratChecker f6101 p6101 = .success := by decide +kernel
theorem unsat6101 : Unsatisfiable (PosFin 65) f6101 := by
  apply lratCheckerSound f6101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6101
  · intro a ha; simp [p6101] at ha; subst a; trivial
  · exact checked6101
theorem derived6101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6101 := by
  apply localUnsat_implies_entails f6101 [c6099, c6096, c6066, c6100, c3557, c3505, c4398] c6101 unsat6101 (by rfl) a
  have h0 : Entails.eval a c6099 := derived6099 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6066 := derived6066 a h
  have h3 : Entails.eval a c6100 := derived6100 a h
  have h4 : Entails.eval a c3557 := h 3556 (by decide)
  have h5 : Entails.eval a c3505 := h 3504 (by decide)
  have h6 : Entails.eval a c4398 := h 4397 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6102 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨34, by decide⟩, true), (⟨42, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3951, some c3557, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6102 : lratChecker f6102 p6102 = .success := by decide +kernel
theorem unsat6102 : Unsatisfiable (PosFin 65) f6102 := by
  apply lratCheckerSound f6102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6102
  · intro a ha; simp [p6102] at ha; subst a; trivial
  · exact checked6102
theorem derived6102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6102 := by
  apply localUnsat_implies_entails f6102 [c3951, c3557] c6102 unsat6102 (by rfl) a
  have h0 : Entails.eval a c3951 := h 3950 (by decide)
  have h1 : Entails.eval a c3557 := h 3556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6103 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6096, some c6066, some c6099, some c6101, some c6102, some c3548, some c3942, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6103 : lratChecker f6103 p6103 = .success := by decide +kernel
theorem unsat6103 : Unsatisfiable (PosFin 65) f6103 := by
  apply lratCheckerSound f6103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6103
  · intro a ha; simp [p6103] at ha; subst a; trivial
  · exact checked6103
theorem derived6103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6103 := by
  apply localUnsat_implies_entails f6103 [c6096, c6066, c6099, c6101, c6102, c3548, c3942] c6103 unsat6103 (by rfl) a
  have h0 : Entails.eval a c6096 := derived6096 a h
  have h1 : Entails.eval a c6066 := derived6066 a h
  have h2 : Entails.eval a c6099 := derived6099 a h
  have h3 : Entails.eval a c6101 := derived6101 a h
  have h4 : Entails.eval a c6102 := derived6102 a h
  have h5 : Entails.eval a c3548 := h 3547 (by decide)
  have h6 : Entails.eval a c3942 := h 3941 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6104 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨59, by decide⟩, true), (⟨37, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5041, some c5567, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6104 : lratChecker f6104 p6104 = .success := by decide +kernel
theorem unsat6104 : Unsatisfiable (PosFin 65) f6104 := by
  apply lratCheckerSound f6104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6104
  · intro a ha; simp [p6104] at ha; subst a; trivial
  · exact checked6104
theorem derived6104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6104 := by
  apply localUnsat_implies_entails f6104 [c5041, c5567] c6104 unsat6104 (by rfl) a
  have h0 : Entails.eval a c5041 := h 5040 (by decide)
  have h1 : Entails.eval a c5567 := h 5566 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6105 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨42, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5073, some c4248, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6105 : lratChecker f6105 p6105 = .success := by decide +kernel
theorem unsat6105 : Unsatisfiable (PosFin 65) f6105 := by
  apply lratCheckerSound f6105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6105
  · intro a ha; simp [p6105] at ha; subst a; trivial
  · exact checked6105
theorem derived6105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6105 := by
  apply localUnsat_implies_entails f6105 [c5073, c4248] c6105 unsat6105 (by rfl) a
  have h0 : Entails.eval a c5073 := h 5072 (by decide)
  have h1 : Entails.eval a c4248 := h 4247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6106 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨54, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4758, some c4082, some c4759, some c4078, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6106 : lratChecker f6106 p6106 = .success := by decide +kernel
theorem unsat6106 : Unsatisfiable (PosFin 65) f6106 := by
  apply lratCheckerSound f6106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6106
  · intro a ha; simp [p6106] at ha; subst a; trivial
  · exact checked6106
theorem derived6106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6106 := by
  apply localUnsat_implies_entails f6106 [c4758, c4082, c4759, c4078] c6106 unsat6106 (by rfl) a
  have h0 : Entails.eval a c4758 := h 4757 (by decide)
  have h1 : Entails.eval a c4082 := h 4081 (by decide)
  have h2 : Entails.eval a c4759 := h 4758 (by decide)
  have h3 : Entails.eval a c4078 := h 4077 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6107 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4990, some c3963, some c4101, some c4511, some c3521, some c3548, some c6105, some c5041, some c6104, some c6106, some c5059, some c5069, some c4608, some c3871, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6107 : lratChecker f6107 p6107 = .success := by decide +kernel
theorem unsat6107 : Unsatisfiable (PosFin 65) f6107 := by
  apply lratCheckerSound f6107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6107
  · intro a ha; simp [p6107] at ha; subst a; trivial
  · exact checked6107
theorem derived6107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6107 := by
  apply localUnsat_implies_entails f6107 [c4990, c3963, c4101, c4511, c3521, c3548, c6105, c5041, c6104, c6106, c5059, c5069, c4608, c3871] c6107 unsat6107 (by rfl) a
  have h0 : Entails.eval a c4990 := h 4989 (by decide)
  have h1 : Entails.eval a c3963 := h 3962 (by decide)
  have h2 : Entails.eval a c4101 := h 4100 (by decide)
  have h3 : Entails.eval a c4511 := h 4510 (by decide)
  have h4 : Entails.eval a c3521 := h 3520 (by decide)
  have h5 : Entails.eval a c3548 := h 3547 (by decide)
  have h6 : Entails.eval a c6105 := derived6105 a h
  have h7 : Entails.eval a c5041 := h 5040 (by decide)
  have h8 : Entails.eval a c6104 := derived6104 a h
  have h9 : Entails.eval a c6106 := derived6106 a h
  have h10 : Entails.eval a c5059 := h 5058 (by decide)
  have h11 : Entails.eval a c5069 := h 5068 (by decide)
  have h12 : Entails.eval a c4608 := h 4607 (by decide)
  have h13 : Entails.eval a c3871 := h 3870 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6108 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6103, some c6096, some c6066, some c6107, some c4996, some c5106, some c4441, some c3557, some c3528, some c6105, some c4706, some c5018, some c4779, some c6106, some c5059, some c5069, some c3875, some c3871, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6108 : lratChecker f6108 p6108 = .success := by decide +kernel
theorem unsat6108 : Unsatisfiable (PosFin 65) f6108 := by
  apply lratCheckerSound f6108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6108
  · intro a ha; simp [p6108] at ha; subst a; trivial
  · exact checked6108
theorem derived6108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6108 := by
  apply localUnsat_implies_entails f6108 [c6103, c6096, c6066, c6107, c4996, c5106, c4441, c3557, c3528, c6105, c4706, c5018, c4779, c6106, c5059, c5069, c3875, c3871] c6108 unsat6108 (by rfl) a
  have h0 : Entails.eval a c6103 := derived6103 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6066 := derived6066 a h
  have h3 : Entails.eval a c6107 := derived6107 a h
  have h4 : Entails.eval a c4996 := h 4995 (by decide)
  have h5 : Entails.eval a c5106 := h 5105 (by decide)
  have h6 : Entails.eval a c4441 := h 4440 (by decide)
  have h7 : Entails.eval a c3557 := h 3556 (by decide)
  have h8 : Entails.eval a c3528 := h 3527 (by decide)
  have h9 : Entails.eval a c6105 := derived6105 a h
  have h10 : Entails.eval a c4706 := h 4705 (by decide)
  have h11 : Entails.eval a c5018 := h 5017 (by decide)
  have h12 : Entails.eval a c4779 := h 4778 (by decide)
  have h13 : Entails.eval a c6106 := derived6106 a h
  have h14 : Entails.eval a c5059 := h 5058 (by decide)
  have h15 : Entails.eval a c5069 := h 5068 (by decide)
  have h16 : Entails.eval a c3875 := h 3874 (by decide)
  have h17 : Entails.eval a c3871 := h 3870 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6109 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨34, by decide⟩, false), (⟨64, by decide⟩, false), (⟨33, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3505, some c3479, some c3453, some c4848, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6109 : lratChecker f6109 p6109 = .success := by decide +kernel
theorem unsat6109 : Unsatisfiable (PosFin 65) f6109 := by
  apply lratCheckerSound f6109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6109
  · intro a ha; simp [p6109] at ha; subst a; trivial
  · exact checked6109
theorem derived6109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6109 := by
  apply localUnsat_implies_entails f6109 [c3505, c3479, c3453, c4848] c6109 unsat6109 (by rfl) a
  have h0 : Entails.eval a c3505 := h 3504 (by decide)
  have h1 : Entails.eval a c3479 := h 3478 (by decide)
  have h2 : Entails.eval a c3453 := h 3452 (by decide)
  have h3 : Entails.eval a c4848 := h 4847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6110 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6103, some c6096, some c6066, some c6108, some c6109, some c3474, some c3443, some c4990, some c4701, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6110 : lratChecker f6110 p6110 = .success := by decide +kernel
theorem unsat6110 : Unsatisfiable (PosFin 65) f6110 := by
  apply lratCheckerSound f6110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6110
  · intro a ha; simp [p6110] at ha; subst a; trivial
  · exact checked6110
theorem derived6110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6110 := by
  apply localUnsat_implies_entails f6110 [c6103, c6096, c6066, c6108, c6109, c3474, c3443, c4990, c4701] c6110 unsat6110 (by rfl) a
  have h0 : Entails.eval a c6103 := derived6103 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6066 := derived6066 a h
  have h3 : Entails.eval a c6108 := derived6108 a h
  have h4 : Entails.eval a c6109 := derived6109 a h
  have h5 : Entails.eval a c3474 := h 3473 (by decide)
  have h6 : Entails.eval a c3443 := h 3442 (by decide)
  have h7 : Entails.eval a c4990 := h 4989 (by decide)
  have h8 : Entails.eval a c4701 := h 4700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6111 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6110, some c6096, some c6066, some c6109, some c3474, some c3443, some c4805, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6111 : lratChecker f6111 p6111 = .success := by decide +kernel
theorem unsat6111 : Unsatisfiable (PosFin 65) f6111 := by
  apply lratCheckerSound f6111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6111
  · intro a ha; simp [p6111] at ha; subst a; trivial
  · exact checked6111
theorem derived6111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6111 := by
  apply localUnsat_implies_entails f6111 [c6110, c6096, c6066, c6109, c3474, c3443, c4805] c6111 unsat6111 (by rfl) a
  have h0 : Entails.eval a c6110 := derived6110 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6066 := derived6066 a h
  have h3 : Entails.eval a c6109 := derived6109 a h
  have h4 : Entails.eval a c3474 := h 3473 (by decide)
  have h5 : Entails.eval a c3443 := h 3442 (by decide)
  have h6 : Entails.eval a c4805 := h 4804 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6112 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨59, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3548, some c3816, some c3859, some c4527, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6112 : lratChecker f6112 p6112 = .success := by decide +kernel
theorem unsat6112 : Unsatisfiable (PosFin 65) f6112 := by
  apply lratCheckerSound f6112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6112
  · intro a ha; simp [p6112] at ha; subst a; trivial
  · exact checked6112
theorem derived6112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6112 := by
  apply localUnsat_implies_entails f6112 [c3548, c3816, c3859, c4527] c6112 unsat6112 (by rfl) a
  have h0 : Entails.eval a c3548 := h 3547 (by decide)
  have h1 : Entails.eval a c3816 := h 3815 (by decide)
  have h2 : Entails.eval a c3859 := h 3858 (by decide)
  have h3 : Entails.eval a c4527 := h 4526 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6113 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4168, some c6112, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6113 : lratChecker f6113 p6113 = .success := by decide +kernel
theorem unsat6113 : Unsatisfiable (PosFin 65) f6113 := by
  apply lratCheckerSound f6113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6113
  · intro a ha; simp [p6113] at ha; subst a; trivial
  · exact checked6113
theorem derived6113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6113 := by
  apply localUnsat_implies_entails f6113 [c4168, c6112] c6113 unsat6113 (by rfl) a
  have h0 : Entails.eval a c4168 := h 4167 (by decide)
  have h1 : Entails.eval a c6112 := derived6112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6114 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false), (⟨59, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3557, some c3820, some c3862, some c4530, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6114 : lratChecker f6114 p6114 = .success := by decide +kernel
theorem unsat6114 : Unsatisfiable (PosFin 65) f6114 := by
  apply lratCheckerSound f6114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6114
  · intro a ha; simp [p6114] at ha; subst a; trivial
  · exact checked6114
theorem derived6114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6114 := by
  apply localUnsat_implies_entails f6114 [c3557, c3820, c3862, c4530] c6114 unsat6114 (by rfl) a
  have h0 : Entails.eval a c3557 := h 3556 (by decide)
  have h1 : Entails.eval a c3820 := h 3819 (by decide)
  have h2 : Entails.eval a c3862 := h 3861 (by decide)
  have h3 : Entails.eval a c4530 := h 4529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6115 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6096, some c6066, some c6110, some c6111, some c6113, some c4173, some c6114, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6115 : lratChecker f6115 p6115 = .success := by decide +kernel
theorem unsat6115 : Unsatisfiable (PosFin 65) f6115 := by
  apply lratCheckerSound f6115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6115
  · intro a ha; simp [p6115] at ha; subst a; trivial
  · exact checked6115
theorem derived6115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6115 := by
  apply localUnsat_implies_entails f6115 [c6096, c6066, c6110, c6111, c6113, c4173, c6114] c6115 unsat6115 (by rfl) a
  have h0 : Entails.eval a c6096 := derived6096 a h
  have h1 : Entails.eval a c6066 := derived6066 a h
  have h2 : Entails.eval a c6110 := derived6110 a h
  have h3 : Entails.eval a c6111 := derived6111 a h
  have h4 : Entails.eval a c6113 := derived6113 a h
  have h5 : Entails.eval a c4173 := h 4172 (by decide)
  have h6 : Entails.eval a c6114 := derived6114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6116 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5957, some c6088, some c4575, some c5024, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6116 : lratChecker f6116 p6116 = .success := by decide +kernel
theorem unsat6116 : Unsatisfiable (PosFin 65) f6116 := by
  apply lratCheckerSound f6116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6116
  · intro a ha; simp [p6116] at ha; subst a; trivial
  · exact checked6116
theorem derived6116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6116 := by
  apply localUnsat_implies_entails f6116 [c5957, c6088, c4575, c5024] c6116 unsat6116 (by rfl) a
  have h0 : Entails.eval a c5957 := derived5957 a h
  have h1 : Entails.eval a c6088 := derived6088 a h
  have h2 : Entails.eval a c4575 := h 4574 (by decide)
  have h3 : Entails.eval a c5024 := h 5023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6117 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6115, some c6096, some c6066, some c3700, some c5277, some c5476, some c3655, some c3968, some c6010, some c3603, some c6087, some c6116, some c3778, some c5245, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6117 : lratChecker f6117 p6117 = .success := by decide +kernel
theorem unsat6117 : Unsatisfiable (PosFin 65) f6117 := by
  apply lratCheckerSound f6117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6117
  · intro a ha; simp [p6117] at ha; subst a; trivial
  · exact checked6117
theorem derived6117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6117 := by
  apply localUnsat_implies_entails f6117 [c6115, c6096, c6066, c3700, c5277, c5476, c3655, c3968, c6010, c3603, c6087, c6116, c3778, c5245] c6117 unsat6117 (by rfl) a
  have h0 : Entails.eval a c6115 := derived6115 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6066 := derived6066 a h
  have h3 : Entails.eval a c3700 := h 3699 (by decide)
  have h4 : Entails.eval a c5277 := h 5276 (by decide)
  have h5 : Entails.eval a c5476 := h 5475 (by decide)
  have h6 : Entails.eval a c3655 := h 3654 (by decide)
  have h7 : Entails.eval a c3968 := h 3967 (by decide)
  have h8 : Entails.eval a c6010 := derived6010 a h
  have h9 : Entails.eval a c3603 := h 3602 (by decide)
  have h10 : Entails.eval a c6087 := derived6087 a h
  have h11 : Entails.eval a c6116 := derived6116 a h
  have h12 : Entails.eval a c3778 := h 3777 (by decide)
  have h13 : Entails.eval a c5245 := h 5244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6118 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨40, by decide⟩, false), (⟨59, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3603, some c3729, some c4974, some c5106, some c3655, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6118 : lratChecker f6118 p6118 = .success := by decide +kernel
theorem unsat6118 : Unsatisfiable (PosFin 65) f6118 := by
  apply lratCheckerSound f6118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6118
  · intro a ha; simp [p6118] at ha; subst a; trivial
  · exact checked6118
theorem derived6118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6118 := by
  apply localUnsat_implies_entails f6118 [c3603, c3729, c4974, c5106, c3655] c6118 unsat6118 (by rfl) a
  have h0 : Entails.eval a c3603 := h 3602 (by decide)
  have h1 : Entails.eval a c3729 := h 3728 (by decide)
  have h2 : Entails.eval a c4974 := h 4973 (by decide)
  have h3 : Entails.eval a c5106 := h 5105 (by decide)
  have h4 : Entails.eval a c3655 := h 3654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6119 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6115, some c6117, some c6118, some c4514, some c5339, some c3968, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6119 : lratChecker f6119 p6119 = .success := by decide +kernel
theorem unsat6119 : Unsatisfiable (PosFin 65) f6119 := by
  apply lratCheckerSound f6119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6119
  · intro a ha; simp [p6119] at ha; subst a; trivial
  · exact checked6119
theorem derived6119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6119 := by
  apply localUnsat_implies_entails f6119 [c6115, c6117, c6118, c4514, c5339, c3968] c6119 unsat6119 (by rfl) a
  have h0 : Entails.eval a c6115 := derived6115 a h
  have h1 : Entails.eval a c6117 := derived6117 a h
  have h2 : Entails.eval a c6118 := derived6118 a h
  have h3 : Entails.eval a c4514 := h 4513 (by decide)
  have h4 : Entails.eval a c5339 := h 5338 (by decide)
  have h5 : Entails.eval a c3968 := h 3967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6120 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6115, some c6119, some c6013, some c3655, some c3714, some c5277, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6120 : lratChecker f6120 p6120 = .success := by decide +kernel
theorem unsat6120 : Unsatisfiable (PosFin 65) f6120 := by
  apply lratCheckerSound f6120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6120
  · intro a ha; simp [p6120] at ha; subst a; trivial
  · exact checked6120
theorem derived6120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6120 := by
  apply localUnsat_implies_entails f6120 [c6115, c6119, c6013, c3655, c3714, c5277] c6120 unsat6120 (by rfl) a
  have h0 : Entails.eval a c6115 := derived6115 a h
  have h1 : Entails.eval a c6119 := derived6119 a h
  have h2 : Entails.eval a c6013 := derived6013 a h
  have h3 : Entails.eval a c3655 := h 3654 (by decide)
  have h4 : Entails.eval a c3714 := h 3713 (by decide)
  have h5 : Entails.eval a c5277 := h 5276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6121 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨57, by decide⟩, false), (⟨35, by decide⟩, true), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3995, some c4401, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p6121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6121 : lratChecker f6121 p6121 = .success := by decide +kernel
theorem unsat6121 : Unsatisfiable (PosFin 65) f6121 := by
  apply lratCheckerSound f6121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6121
  · intro a ha; simp [p6121] at ha; subst a; trivial
  · exact checked6121
theorem derived6121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6121 := by
  apply localUnsat_implies_entails f6121 [c3995, c4401] c6121 unsat6121 (by rfl) a
  have h0 : Entails.eval a c3995 := h 3994 (by decide)
  have h1 : Entails.eval a c4401 := h 4400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6122 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨44, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, true), (⟨34, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4533, some c4298, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6122 : lratChecker f6122 p6122 = .success := by decide +kernel
theorem unsat6122 : Unsatisfiable (PosFin 65) f6122 := by
  apply lratCheckerSound f6122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6122
  · intro a ha; simp [p6122] at ha; subst a; trivial
  · exact checked6122
theorem derived6122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6122 := by
  apply localUnsat_implies_entails f6122 [c4533, c4298] c6122 unsat6122 (by rfl) a
  have h0 : Entails.eval a c4533 := h 4532 (by decide)
  have h1 : Entails.eval a c4298 := h 4297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6123 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4920, some c4302, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6123 : lratChecker f6123 p6123 = .success := by decide +kernel
theorem unsat6123 : Unsatisfiable (PosFin 65) f6123 := by
  apply lratCheckerSound f6123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6123
  · intro a ha; simp [p6123] at ha; subst a; trivial
  · exact checked6123
theorem derived6123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6123 := by
  apply localUnsat_implies_entails f6123 [c4920, c4302] c6123 unsat6123 (by rfl) a
  have h0 : Entails.eval a c4920 := h 4919 (by decide)
  have h1 : Entails.eval a c4302 := h 4301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6124 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨40, by decide⟩, true), (⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6123, some c3739, some c3735, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6124 : lratChecker f6124 p6124 = .success := by decide +kernel
theorem unsat6124 : Unsatisfiable (PosFin 65) f6124 := by
  apply lratCheckerSound f6124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6124
  · intro a ha; simp [p6124] at ha; subst a; trivial
  · exact checked6124
theorem derived6124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6124 := by
  apply localUnsat_implies_entails f6124 [c6123, c3739, c3735] c6124 unsat6124 (by rfl) a
  have h0 : Entails.eval a c6123 := derived6123 a h
  have h1 : Entails.eval a c3739 := h 3738 (by decide)
  have h2 : Entails.eval a c3735 := h 3734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6125 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨35, by decide⟩, true), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨37, by decide⟩, true), (⟨45, by decide⟩, true), (⟨34, by decide⟩, false), (⟨42, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6122, some c6121, some c5804, some c4303, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6125 : lratChecker f6125 p6125 = .success := by decide +kernel
theorem unsat6125 : Unsatisfiable (PosFin 65) f6125 := by
  apply lratCheckerSound f6125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6125
  · intro a ha; simp [p6125] at ha; subst a; trivial
  · exact checked6125
theorem derived6125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6125 := by
  apply localUnsat_implies_entails f6125 [c6122, c6121, c5804, c4303] c6125 unsat6125 (by rfl) a
  have h0 : Entails.eval a c6122 := derived6122 a h
  have h1 : Entails.eval a c6121 := derived6121 a h
  have h2 : Entails.eval a c5804 := h 5803 (by decide)
  have h3 : Entails.eval a c4303 := h 4302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6126 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨58, by decide⟩, true), (⟨43, by decide⟩, false), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨38, by decide⟩, false), (⟨59, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5432, some c5820, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6126 : lratChecker f6126 p6126 = .success := by decide +kernel
theorem unsat6126 : Unsatisfiable (PosFin 65) f6126 := by
  apply lratCheckerSound f6126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6126
  · intro a ha; simp [p6126] at ha; subst a; trivial
  · exact checked6126
theorem derived6126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6126 := by
  apply localUnsat_implies_entails f6126 [c5432, c5820] c6126 unsat6126 (by rfl) a
  have h0 : Entails.eval a c5432 := h 5431 (by decide)
  have h1 : Entails.eval a c5820 := h 5819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6127 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6120, some c6115, some c6096, some c6066, some c6013, some c3655, some c3714, some c4974, some c4130, some c3603, some c4663, some c5339, some c6010, some c4398, some c6124, some c6125, some c6059, some c5792, some c5909, some c6126, some c3739, some c5802, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked6127 : lratChecker f6127 p6127 = .success := by decide +kernel
theorem unsat6127 : Unsatisfiable (PosFin 65) f6127 := by
  apply lratCheckerSound f6127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6127
  · intro a ha; simp [p6127] at ha; subst a; trivial
  · exact checked6127
theorem derived6127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6127 := by
  apply localUnsat_implies_entails f6127 [c6120, c6115, c6096, c6066, c6013, c3655, c3714, c4974, c4130, c3603, c4663, c5339, c6010, c4398, c6124, c6125, c6059, c5792, c5909, c6126, c3739, c5802] c6127 unsat6127 (by rfl) a
  have h0 : Entails.eval a c6120 := derived6120 a h
  have h1 : Entails.eval a c6115 := derived6115 a h
  have h2 : Entails.eval a c6096 := derived6096 a h
  have h3 : Entails.eval a c6066 := derived6066 a h
  have h4 : Entails.eval a c6013 := derived6013 a h
  have h5 : Entails.eval a c3655 := h 3654 (by decide)
  have h6 : Entails.eval a c3714 := h 3713 (by decide)
  have h7 : Entails.eval a c4974 := h 4973 (by decide)
  have h8 : Entails.eval a c4130 := h 4129 (by decide)
  have h9 : Entails.eval a c3603 := h 3602 (by decide)
  have h10 : Entails.eval a c4663 := h 4662 (by decide)
  have h11 : Entails.eval a c5339 := h 5338 (by decide)
  have h12 : Entails.eval a c6010 := derived6010 a h
  have h13 : Entails.eval a c4398 := h 4397 (by decide)
  have h14 : Entails.eval a c6124 := derived6124 a h
  have h15 : Entails.eval a c6125 := derived6125 a h
  have h16 : Entails.eval a c6059 := derived6059 a h
  have h17 : Entails.eval a c5792 := h 5791 (by decide)
  have h18 : Entails.eval a c5909 := derived5909 a h
  have h19 : Entails.eval a c6126 := derived6126 a h
  have h20 : Entails.eval a c3739 := h 3738 (by decide)
  have h21 : Entails.eval a c5802 := h 5801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6128 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6115, some c6120, some c6127, some c6097, some c4173, some c5106, some c4996, some c3655, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6128 : lratChecker f6128 p6128 = .success := by decide +kernel
theorem unsat6128 : Unsatisfiable (PosFin 65) f6128 := by
  apply lratCheckerSound f6128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6128
  · intro a ha; simp [p6128] at ha; subst a; trivial
  · exact checked6128
theorem derived6128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6128 := by
  apply localUnsat_implies_entails f6128 [c6115, c6120, c6127, c6097, c4173, c5106, c4996, c3655] c6128 unsat6128 (by rfl) a
  have h0 : Entails.eval a c6115 := derived6115 a h
  have h1 : Entails.eval a c6120 := derived6120 a h
  have h2 : Entails.eval a c6127 := derived6127 a h
  have h3 : Entails.eval a c6097 := derived6097 a h
  have h4 : Entails.eval a c4173 := h 4172 (by decide)
  have h5 : Entails.eval a c5106 := h 5105 (by decide)
  have h6 : Entails.eval a c4996 := h 4995 (by decide)
  have h7 : Entails.eval a c3655 := h 3654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6129 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨37, by decide⟩, false), (⟨34, by decide⟩, true), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4168, some c6105, some c4990, some c3963, some c4101, some c4511, some c5041, some c3726, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6129 : lratChecker f6129 p6129 = .success := by decide +kernel
theorem unsat6129 : Unsatisfiable (PosFin 65) f6129 := by
  apply lratCheckerSound f6129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6129
  · intro a ha; simp [p6129] at ha; subst a; trivial
  · exact checked6129
theorem derived6129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6129 := by
  apply localUnsat_implies_entails f6129 [c4168, c6105, c4990, c3963, c4101, c4511, c5041, c3726] c6129 unsat6129 (by rfl) a
  have h0 : Entails.eval a c4168 := h 4167 (by decide)
  have h1 : Entails.eval a c6105 := derived6105 a h
  have h2 : Entails.eval a c4990 := h 4989 (by decide)
  have h3 : Entails.eval a c3963 := h 3962 (by decide)
  have h4 : Entails.eval a c4101 := h 4100 (by decide)
  have h5 : Entails.eval a c4511 := h 4510 (by decide)
  have h6 : Entails.eval a c5041 := h 5040 (by decide)
  have h7 : Entails.eval a c3726 := h 3725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6130 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨42, by decide⟩, false), (⟨34, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3963, some c4101, some c4590, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6130 : lratChecker f6130 p6130 = .success := by decide +kernel
theorem unsat6130 : Unsatisfiable (PosFin 65) f6130 := by
  apply lratCheckerSound f6130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6130
  · intro a ha; simp [p6130] at ha; subst a; trivial
  · exact checked6130
theorem derived6130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6130 := by
  apply localUnsat_implies_entails f6130 [c3963, c4101, c4590] c6130 unsat6130 (by rfl) a
  have h0 : Entails.eval a c3963 := h 3962 (by decide)
  have h1 : Entails.eval a c4101 := h 4100 (by decide)
  have h2 : Entails.eval a c4590 := h 4589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6131 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨34, by decide⟩, true), (⟨63, by decide⟩, false), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6129, some c6130, some c4990, some c5367, some c5389, some c3791, some c4590, some c6104, some c4527, some c5013, some c3697, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p6131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6131 : lratChecker f6131 p6131 = .success := by decide +kernel
theorem unsat6131 : Unsatisfiable (PosFin 65) f6131 := by
  apply lratCheckerSound f6131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6131
  · intro a ha; simp [p6131] at ha; subst a; trivial
  · exact checked6131
theorem derived6131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6131 := by
  apply localUnsat_implies_entails f6131 [c6129, c6130, c4990, c5367, c5389, c3791, c4590, c6104, c4527, c5013, c3697] c6131 unsat6131 (by rfl) a
  have h0 : Entails.eval a c6129 := derived6129 a h
  have h1 : Entails.eval a c6130 := derived6130 a h
  have h2 : Entails.eval a c4990 := h 4989 (by decide)
  have h3 : Entails.eval a c5367 := h 5366 (by decide)
  have h4 : Entails.eval a c5389 := h 5388 (by decide)
  have h5 : Entails.eval a c3791 := h 3790 (by decide)
  have h6 : Entails.eval a c4590 := h 4589 (by decide)
  have h7 : Entails.eval a c6104 := derived6104 a h
  have h8 : Entails.eval a c4527 := h 4526 (by decide)
  have h9 : Entails.eval a c5013 := h 5012 (by decide)
  have h10 : Entails.eval a c3697 := h 3696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6132 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6128, some c6115, some c6096, some c6066, some c6131, some c3596, some c6097, some c3942, some c4569, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6132 : lratChecker f6132 p6132 = .success := by decide +kernel
theorem unsat6132 : Unsatisfiable (PosFin 65) f6132 := by
  apply lratCheckerSound f6132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6132
  · intro a ha; simp [p6132] at ha; subst a; trivial
  · exact checked6132
theorem derived6132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6132 := by
  apply localUnsat_implies_entails f6132 [c6128, c6115, c6096, c6066, c6131, c3596, c6097, c3942, c4569] c6132 unsat6132 (by rfl) a
  have h0 : Entails.eval a c6128 := derived6128 a h
  have h1 : Entails.eval a c6115 := derived6115 a h
  have h2 : Entails.eval a c6096 := derived6096 a h
  have h3 : Entails.eval a c6066 := derived6066 a h
  have h4 : Entails.eval a c6131 := derived6131 a h
  have h5 : Entails.eval a c3596 := h 3595 (by decide)
  have h6 : Entails.eval a c6097 := derived6097 a h
  have h7 : Entails.eval a c3942 := h 3941 (by decide)
  have h8 : Entails.eval a c4569 := h 4568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6133 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3596, some c3627, some c4929, some c4313, some c4684, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6133 : lratChecker f6133 p6133 = .success := by decide +kernel
theorem unsat6133 : Unsatisfiable (PosFin 65) f6133 := by
  apply lratCheckerSound f6133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6133
  · intro a ha; simp [p6133] at ha; subst a; trivial
  · exact checked6133
theorem derived6133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6133 := by
  apply localUnsat_implies_entails f6133 [c3596, c3627, c4929, c4313, c4684] c6133 unsat6133 (by rfl) a
  have h0 : Entails.eval a c3596 := h 3595 (by decide)
  have h1 : Entails.eval a c3627 := h 3626 (by decide)
  have h2 : Entails.eval a c4929 := h 4928 (by decide)
  have h3 : Entails.eval a c4313 := h 4312 (by decide)
  have h4 : Entails.eval a c4684 := h 4683 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6134 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6066, some c6096, some c6115, some c6128, some c6132, some c6133, some c4990, some c4511, some c5939, some c3646, some c5717, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6134 : lratChecker f6134 p6134 = .success := by decide +kernel
theorem unsat6134 : Unsatisfiable (PosFin 65) f6134 := by
  apply lratCheckerSound f6134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6134
  · intro a ha; simp [p6134] at ha; subst a; trivial
  · exact checked6134
theorem derived6134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6134 := by
  apply localUnsat_implies_entails f6134 [c6066, c6096, c6115, c6128, c6132, c6133, c4990, c4511, c5939, c3646, c5717] c6134 unsat6134 (by rfl) a
  have h0 : Entails.eval a c6066 := derived6066 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6115 := derived6115 a h
  have h3 : Entails.eval a c6128 := derived6128 a h
  have h4 : Entails.eval a c6132 := derived6132 a h
  have h5 : Entails.eval a c6133 := derived6133 a h
  have h6 : Entails.eval a c4990 := h 4989 (by decide)
  have h7 : Entails.eval a c4511 := h 4510 (by decide)
  have h8 : Entails.eval a c5939 := derived5939 a h
  have h9 : Entails.eval a c3646 := h 3645 (by decide)
  have h10 : Entails.eval a c5717 := h 5716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6135 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6132, some c6128, some c6115, some c6096, some c6066, some c6134, some c3755, some c4929, some c4829, some c5733, some c4313, some c4846, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6135 : lratChecker f6135 p6135 = .success := by decide +kernel
theorem unsat6135 : Unsatisfiable (PosFin 65) f6135 := by
  apply lratCheckerSound f6135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6135
  · intro a ha; simp [p6135] at ha; subst a; trivial
  · exact checked6135
theorem derived6135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6135 := by
  apply localUnsat_implies_entails f6135 [c6132, c6128, c6115, c6096, c6066, c6134, c3755, c4929, c4829, c5733, c4313, c4846] c6135 unsat6135 (by rfl) a
  have h0 : Entails.eval a c6132 := derived6132 a h
  have h1 : Entails.eval a c6128 := derived6128 a h
  have h2 : Entails.eval a c6115 := derived6115 a h
  have h3 : Entails.eval a c6096 := derived6096 a h
  have h4 : Entails.eval a c6066 := derived6066 a h
  have h5 : Entails.eval a c6134 := derived6134 a h
  have h6 : Entails.eval a c3755 := h 3754 (by decide)
  have h7 : Entails.eval a c4929 := h 4928 (by decide)
  have h8 : Entails.eval a c4829 := h 4828 (by decide)
  have h9 : Entails.eval a c5733 := h 5732 (by decide)
  have h10 : Entails.eval a c4313 := h 4312 (by decide)
  have h11 : Entails.eval a c4846 := h 4845 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6136 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3928, some c6133, some c3755, some c4805, some c4313, some c6018, some c6104, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6136 : lratChecker f6136 p6136 = .success := by decide +kernel
theorem unsat6136 : Unsatisfiable (PosFin 65) f6136 := by
  apply lratCheckerSound f6136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6136
  · intro a ha; simp [p6136] at ha; subst a; trivial
  · exact checked6136
theorem derived6136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6136 := by
  apply localUnsat_implies_entails f6136 [c3928, c6133, c3755, c4805, c4313, c6018, c6104] c6136 unsat6136 (by rfl) a
  have h0 : Entails.eval a c3928 := h 3927 (by decide)
  have h1 : Entails.eval a c6133 := derived6133 a h
  have h2 : Entails.eval a c3755 := h 3754 (by decide)
  have h3 : Entails.eval a c4805 := h 4804 (by decide)
  have h4 : Entails.eval a c4313 := h 4312 (by decide)
  have h5 : Entails.eval a c6018 := derived6018 a h
  have h6 : Entails.eval a c6104 := derived6104 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6137 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3646, some c5245, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6137 : lratChecker f6137 p6137 = .success := by decide +kernel
theorem unsat6137 : Unsatisfiable (PosFin 65) f6137 := by
  apply lratCheckerSound f6137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6137
  · intro a ha; simp [p6137] at ha; subst a; trivial
  · exact checked6137
theorem derived6137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6137 := by
  apply localUnsat_implies_entails f6137 [c3646, c5245] c6137 unsat6137 (by rfl) a
  have h0 : Entails.eval a c3646 := h 3645 (by decide)
  have h1 : Entails.eval a c5245 := h 5244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6138 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, false), (⟨59, by decide⟩, true), (⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3928, some c6133, some c6136, some c4990, some c6137, some c4701, some c3643, some c4218, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6138 : lratChecker f6138 p6138 = .success := by decide +kernel
theorem unsat6138 : Unsatisfiable (PosFin 65) f6138 := by
  apply lratCheckerSound f6138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6138
  · intro a ha; simp [p6138] at ha; subst a; trivial
  · exact checked6138
theorem derived6138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6138 := by
  apply localUnsat_implies_entails f6138 [c3928, c6133, c6136, c4990, c6137, c4701, c3643, c4218] c6138 unsat6138 (by rfl) a
  have h0 : Entails.eval a c3928 := h 3927 (by decide)
  have h1 : Entails.eval a c6133 := derived6133 a h
  have h2 : Entails.eval a c6136 := derived6136 a h
  have h3 : Entails.eval a c4990 := h 4989 (by decide)
  have h4 : Entails.eval a c6137 := derived6137 a h
  have h5 : Entails.eval a c4701 := h 4700 (by decide)
  have h6 : Entails.eval a c3643 := h 3642 (by decide)
  have h7 : Entails.eval a c4218 := h 4217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6139 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6066, some c6096, some c6115, some c6128, some c6132, some c6133, some c6135, some c3928, some c6138, some c4007, some c4373, some c3755, some c5939, some c4990, some c3646, some c5245, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6139 : lratChecker f6139 p6139 = .success := by decide +kernel
theorem unsat6139 : Unsatisfiable (PosFin 65) f6139 := by
  apply lratCheckerSound f6139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6139
  · intro a ha; simp [p6139] at ha; subst a; trivial
  · exact checked6139
theorem derived6139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6139 := by
  apply localUnsat_implies_entails f6139 [c6066, c6096, c6115, c6128, c6132, c6133, c6135, c3928, c6138, c4007, c4373, c3755, c5939, c4990, c3646, c5245] c6139 unsat6139 (by rfl) a
  have h0 : Entails.eval a c6066 := derived6066 a h
  have h1 : Entails.eval a c6096 := derived6096 a h
  have h2 : Entails.eval a c6115 := derived6115 a h
  have h3 : Entails.eval a c6128 := derived6128 a h
  have h4 : Entails.eval a c6132 := derived6132 a h
  have h5 : Entails.eval a c6133 := derived6133 a h
  have h6 : Entails.eval a c6135 := derived6135 a h
  have h7 : Entails.eval a c3928 := h 3927 (by decide)
  have h8 : Entails.eval a c6138 := derived6138 a h
  have h9 : Entails.eval a c4007 := h 4006 (by decide)
  have h10 : Entails.eval a c4373 := h 4372 (by decide)
  have h11 : Entails.eval a c3755 := h 3754 (by decide)
  have h12 : Entails.eval a c5939 := derived5939 a h
  have h13 : Entails.eval a c4990 := h 4989 (by decide)
  have h14 : Entails.eval a c3646 := h 3645 (by decide)
  have h15 : Entails.eval a c5245 := h 5244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6140 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3690, some c4968, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6140 : lratChecker f6140 p6140 = .success := by decide +kernel
theorem unsat6140 : Unsatisfiable (PosFin 65) f6140 := by
  apply lratCheckerSound f6140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6140
  · intro a ha; simp [p6140] at ha; subst a; trivial
  · exact checked6140
theorem derived6140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6140 := by
  apply localUnsat_implies_entails f6140 [c3690, c4968] c6140 unsat6140 (by rfl) a
  have h0 : Entails.eval a c3690 := h 3689 (by decide)
  have h1 : Entails.eval a c4968 := h 4967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6141 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3163, some c3186, some c3155, some c3318, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6141 : lratChecker f6141 p6141 = .success := by decide +kernel
theorem unsat6141 : Unsatisfiable (PosFin 65) f6141 := by
  apply lratCheckerSound f6141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6141
  · intro a ha; simp [p6141] at ha; subst a; trivial
  · exact checked6141
theorem derived6141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6141 := by
  apply localUnsat_implies_entails f6141 [c3163, c3186, c3155, c3318] c6141 unsat6141 (by rfl) a
  have h0 : Entails.eval a c3163 := h 3162 (by decide)
  have h1 : Entails.eval a c3186 := h 3185 (by decide)
  have h2 : Entails.eval a c3155 := h 3154 (by decide)
  have h3 : Entails.eval a c3318 := h 3317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6142 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨20, by decide⟩, true), (⟨30, by decide⟩, false), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3399, some c3401, some c3230, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6142 : lratChecker f6142 p6142 = .success := by decide +kernel
theorem unsat6142 : Unsatisfiable (PosFin 65) f6142 := by
  apply lratCheckerSound f6142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6142
  · intro a ha; simp [p6142] at ha; subst a; trivial
  · exact checked6142
theorem derived6142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6142 := by
  apply localUnsat_implies_entails f6142 [c3399, c3401, c3230] c6142 unsat6142 (by rfl) a
  have h0 : Entails.eval a c3399 := h 3398 (by decide)
  have h1 : Entails.eval a c3401 := h 3400 (by decide)
  have h2 : Entails.eval a c3230 := h 3229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6143 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨30, by decide⟩, false), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6142, some c6141, some c3171, some c3183, some c3237, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6143 : lratChecker f6143 p6143 = .success := by decide +kernel
theorem unsat6143 : Unsatisfiable (PosFin 65) f6143 := by
  apply lratCheckerSound f6143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6143
  · intro a ha; simp [p6143] at ha; subst a; trivial
  · exact checked6143
theorem derived6143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6143 := by
  apply localUnsat_implies_entails f6143 [c6142, c6141, c3171, c3183, c3237] c6143 unsat6143 (by rfl) a
  have h0 : Entails.eval a c6142 := derived6142 a h
  have h1 : Entails.eval a c6141 := derived6141 a h
  have h2 : Entails.eval a c3171 := h 3170 (by decide)
  have h3 : Entails.eval a c3183 := h 3182 (by decide)
  have h4 : Entails.eval a c3237 := h 3236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6144 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨57, by decide⟩, false), (⟨64, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6143, some c3134, some c3259, some c3273, some c3186, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6144 : lratChecker f6144 p6144 = .success := by decide +kernel
theorem unsat6144 : Unsatisfiable (PosFin 65) f6144 := by
  apply lratCheckerSound f6144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6144
  · intro a ha; simp [p6144] at ha; subst a; trivial
  · exact checked6144
theorem derived6144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6144 := by
  apply localUnsat_implies_entails f6144 [c6143, c3134, c3259, c3273, c3186] c6144 unsat6144 (by rfl) a
  have h0 : Entails.eval a c6143 := derived6143 a h
  have h1 : Entails.eval a c3134 := h 3133 (by decide)
  have h2 : Entails.eval a c3259 := h 3258 (by decide)
  have h3 : Entails.eval a c3273 := h 3272 (by decide)
  have h4 : Entails.eval a c3186 := h 3185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6145 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨30, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3422, some c3019, some c3129, some c2905, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p6145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6145 : lratChecker f6145 p6145 = .success := by decide +kernel
theorem unsat6145 : Unsatisfiable (PosFin 65) f6145 := by
  apply lratCheckerSound f6145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6145
  · intro a ha; simp [p6145] at ha; subst a; trivial
  · exact checked6145
theorem derived6145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6145 := by
  apply localUnsat_implies_entails f6145 [c3422, c3019, c3129, c2905] c6145 unsat6145 (by rfl) a
  have h0 : Entails.eval a c3422 := h 3421 (by decide)
  have h1 : Entails.eval a c3019 := h 3018 (by decide)
  have h2 : Entails.eval a c3129 := h 3128 (by decide)
  have h3 : Entails.eval a c2905 := h 2904 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6146 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨37, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c4990, some c4950, some c4830, some c5435, some c4846, some c5579, some c5012, some c4115, some c4127, some c4963, some c4142, some c4132, some c6144, some c6145, some c2746, some c2797, some c2823, some c3305, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked6146 : lratChecker f6146 p6146 = .success := by decide +kernel
theorem unsat6146 : Unsatisfiable (PosFin 65) f6146 := by
  apply lratCheckerSound f6146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6146
  · intro a ha; simp [p6146] at ha; subst a; trivial
  · exact checked6146
theorem derived6146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6146 := by
  apply localUnsat_implies_entails f6146 [c6139, c4990, c4950, c4830, c5435, c4846, c5579, c5012, c4115, c4127, c4963, c4142, c4132, c6144, c6145, c2746, c2797, c2823, c3305] c6146 unsat6146 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c4990 := h 4989 (by decide)
  have h2 : Entails.eval a c4950 := h 4949 (by decide)
  have h3 : Entails.eval a c4830 := h 4829 (by decide)
  have h4 : Entails.eval a c5435 := h 5434 (by decide)
  have h5 : Entails.eval a c4846 := h 4845 (by decide)
  have h6 : Entails.eval a c5579 := h 5578 (by decide)
  have h7 : Entails.eval a c5012 := h 5011 (by decide)
  have h8 : Entails.eval a c4115 := h 4114 (by decide)
  have h9 : Entails.eval a c4127 := h 4126 (by decide)
  have h10 : Entails.eval a c4963 := h 4962 (by decide)
  have h11 : Entails.eval a c4142 := h 4141 (by decide)
  have h12 : Entails.eval a c4132 := h 4131 (by decide)
  have h13 : Entails.eval a c6144 := derived6144 a h
  have h14 : Entails.eval a c6145 := derived6145 a h
  have h15 : Entails.eval a c2746 := h 2745 (by decide)
  have h16 : Entails.eval a c2797 := h 2796 (by decide)
  have h17 : Entails.eval a c2823 := h 2822 (by decide)
  have h18 : Entails.eval a c3305 := h 3304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6147 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3596, some c6139, some c3928, some c5252, some c3651, some c4990, some c6140, some c3905, some c4950, some c4830, some c5435, some c4846, some c6104, some c6146, some c3679, some c3712, some c3706, some c3721, some c3707, some c5123, some c4731, some c6144, some c5541, some c6145, some c2746, some c2797, some c2823, some c3301, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked6147 : lratChecker f6147 p6147 = .success := by decide +kernel
theorem unsat6147 : Unsatisfiable (PosFin 65) f6147 := by
  apply lratCheckerSound f6147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6147
  · intro a ha; simp [p6147] at ha; subst a; trivial
  · exact checked6147
theorem derived6147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6147 := by
  apply localUnsat_implies_entails f6147 [c3596, c6139, c3928, c5252, c3651, c4990, c6140, c3905, c4950, c4830, c5435, c4846, c6104, c6146, c3679, c3712, c3706, c3721, c3707, c5123, c4731, c6144, c5541, c6145, c2746, c2797, c2823, c3301] c6147 unsat6147 (by rfl) a
  have h0 : Entails.eval a c3596 := h 3595 (by decide)
  have h1 : Entails.eval a c6139 := derived6139 a h
  have h2 : Entails.eval a c3928 := h 3927 (by decide)
  have h3 : Entails.eval a c5252 := h 5251 (by decide)
  have h4 : Entails.eval a c3651 := h 3650 (by decide)
  have h5 : Entails.eval a c4990 := h 4989 (by decide)
  have h6 : Entails.eval a c6140 := derived6140 a h
  have h7 : Entails.eval a c3905 := h 3904 (by decide)
  have h8 : Entails.eval a c4950 := h 4949 (by decide)
  have h9 : Entails.eval a c4830 := h 4829 (by decide)
  have h10 : Entails.eval a c5435 := h 5434 (by decide)
  have h11 : Entails.eval a c4846 := h 4845 (by decide)
  have h12 : Entails.eval a c6104 := derived6104 a h
  have h13 : Entails.eval a c6146 := derived6146 a h
  have h14 : Entails.eval a c3679 := h 3678 (by decide)
  have h15 : Entails.eval a c3712 := h 3711 (by decide)
  have h16 : Entails.eval a c3706 := h 3705 (by decide)
  have h17 : Entails.eval a c3721 := h 3720 (by decide)
  have h18 : Entails.eval a c3707 := h 3706 (by decide)
  have h19 : Entails.eval a c5123 := h 5122 (by decide)
  have h20 : Entails.eval a c4731 := h 4730 (by decide)
  have h21 : Entails.eval a c6144 := derived6144 a h
  have h22 : Entails.eval a c5541 := h 5540 (by decide)
  have h23 : Entails.eval a c6145 := derived6145 a h
  have h24 : Entails.eval a c2746 := h 2745 (by decide)
  have h25 : Entails.eval a c2797 := h 2796 (by decide)
  have h26 : Entails.eval a c2823 := h 2822 (by decide)
  have h27 : Entails.eval a c3301 := h 3300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6148 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨34, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5123, some c4263, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p6148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6148 : lratChecker f6148 p6148 = .success := by decide +kernel
theorem unsat6148 : Unsatisfiable (PosFin 65) f6148 := by
  apply lratCheckerSound f6148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6148
  · intro a ha; simp [p6148] at ha; subst a; trivial
  · exact checked6148
theorem derived6148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6148 := by
  apply localUnsat_implies_entails f6148 [c5123, c4263] c6148 unsat6148 (by rfl) a
  have h0 : Entails.eval a c5123 := h 5122 (by decide)
  have h1 : Entails.eval a c4263 := h 4262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6149 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c3596, some c3928, some c5252, some c3905, some c3651, some c5435, some c4950, some c4990, some c6104, some c4846, some c6140, some c6147, some c6148, some c5042, some c4743, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6149 : lratChecker f6149 p6149 = .success := by decide +kernel
theorem unsat6149 : Unsatisfiable (PosFin 65) f6149 := by
  apply lratCheckerSound f6149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6149
  · intro a ha; simp [p6149] at ha; subst a; trivial
  · exact checked6149
theorem derived6149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6149 := by
  apply localUnsat_implies_entails f6149 [c6139, c3596, c3928, c5252, c3905, c3651, c5435, c4950, c4990, c6104, c4846, c6140, c6147, c6148, c5042, c4743] c6149 unsat6149 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c3596 := h 3595 (by decide)
  have h2 : Entails.eval a c3928 := h 3927 (by decide)
  have h3 : Entails.eval a c5252 := h 5251 (by decide)
  have h4 : Entails.eval a c3905 := h 3904 (by decide)
  have h5 : Entails.eval a c3651 := h 3650 (by decide)
  have h6 : Entails.eval a c5435 := h 5434 (by decide)
  have h7 : Entails.eval a c4950 := h 4949 (by decide)
  have h8 : Entails.eval a c4990 := h 4989 (by decide)
  have h9 : Entails.eval a c6104 := derived6104 a h
  have h10 : Entails.eval a c4846 := h 4845 (by decide)
  have h11 : Entails.eval a c6140 := derived6140 a h
  have h12 : Entails.eval a c6147 := derived6147 a h
  have h13 : Entails.eval a c6148 := derived6148 a h
  have h14 : Entails.eval a c5042 := h 5041 (by decide)
  have h15 : Entails.eval a c4743 := h 4742 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6150 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4990, some c5455, some c3756, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6150 : lratChecker f6150 p6150 = .success := by decide +kernel
theorem unsat6150 : Unsatisfiable (PosFin 65) f6150 := by
  apply lratCheckerSound f6150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6150
  · intro a ha; simp [p6150] at ha; subst a; trivial
  · exact checked6150
theorem derived6150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6150 := by
  apply localUnsat_implies_entails f6150 [c4990, c5455, c3756] c6150 unsat6150 (by rfl) a
  have h0 : Entails.eval a c4990 := h 4989 (by decide)
  have h1 : Entails.eval a c5455 := h 5454 (by decide)
  have h2 : Entails.eval a c3756 := h 3755 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6151 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨46, by decide⟩, false), (⟨62, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6150, some c3673, some c3651, some c5252, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6151 : lratChecker f6151 p6151 = .success := by decide +kernel
theorem unsat6151 : Unsatisfiable (PosFin 65) f6151 := by
  apply lratCheckerSound f6151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6151
  · intro a ha; simp [p6151] at ha; subst a; trivial
  · exact checked6151
theorem derived6151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6151 := by
  apply localUnsat_implies_entails f6151 [c6150, c3673, c3651, c5252] c6151 unsat6151 (by rfl) a
  have h0 : Entails.eval a c6150 := derived6150 a h
  have h1 : Entails.eval a c3673 := h 3672 (by decide)
  have h2 : Entails.eval a c3651 := h 3650 (by decide)
  have h3 : Entails.eval a c5252 := h 5251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6152 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6151, some c3628, some c6133, some c5455, some c4030, some c6130, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6152 : lratChecker f6152 p6152 = .success := by decide +kernel
theorem unsat6152 : Unsatisfiable (PosFin 65) f6152 := by
  apply lratCheckerSound f6152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6152
  · intro a ha; simp [p6152] at ha; subst a; trivial
  · exact checked6152
theorem derived6152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6152 := by
  apply localUnsat_implies_entails f6152 [c6151, c3628, c6133, c5455, c4030, c6130] c6152 unsat6152 (by rfl) a
  have h0 : Entails.eval a c6151 := derived6151 a h
  have h1 : Entails.eval a c3628 := h 3627 (by decide)
  have h2 : Entails.eval a c6133 := derived6133 a h
  have h3 : Entails.eval a c5455 := h 5454 (by decide)
  have h4 : Entails.eval a c4030 := h 4029 (by decide)
  have h5 : Entails.eval a c6130 := derived6130 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6153 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6149, some c6152, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6153 : lratChecker f6153 p6153 = .success := by decide +kernel
theorem unsat6153 : Unsatisfiable (PosFin 65) f6153 := by
  apply lratCheckerSound f6153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6153
  · intro a ha; simp [p6153] at ha; subst a; trivial
  · exact checked6153
theorem derived6153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6153 := by
  apply localUnsat_implies_entails f6153 [c6139, c6149, c6152] c6153 unsat6153 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6149 := derived6149 a h
  have h2 : Entails.eval a c6152 := derived6152 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6154 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4312, some c5458, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6154 : lratChecker f6154 p6154 = .success := by decide +kernel
theorem unsat6154 : Unsatisfiable (PosFin 65) f6154 := by
  apply lratCheckerSound f6154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6154
  · intro a ha; simp [p6154] at ha; subst a; trivial
  · exact checked6154
theorem derived6154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6154 := by
  apply localUnsat_implies_entails f6154 [c4312, c5458] c6154 unsat6154 (by rfl) a
  have h0 : Entails.eval a c4312 := h 4311 (by decide)
  have h1 : Entails.eval a c5458 := h 5457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6155 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨46, by decide⟩, false), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6153, some c6067, some c3652, some c5336, some c5390, some c4170, some c4658, some c4349, some c4393, some c6154, some c4411, some c3759, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6155 : lratChecker f6155 p6155 = .success := by decide +kernel
theorem unsat6155 : Unsatisfiable (PosFin 65) f6155 := by
  apply lratCheckerSound f6155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6155
  · intro a ha; simp [p6155] at ha; subst a; trivial
  · exact checked6155
theorem derived6155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6155 := by
  apply localUnsat_implies_entails f6155 [c6153, c6067, c3652, c5336, c5390, c4170, c4658, c4349, c4393, c6154, c4411, c3759] c6155 unsat6155 (by rfl) a
  have h0 : Entails.eval a c6153 := derived6153 a h
  have h1 : Entails.eval a c6067 := derived6067 a h
  have h2 : Entails.eval a c3652 := h 3651 (by decide)
  have h3 : Entails.eval a c5336 := h 5335 (by decide)
  have h4 : Entails.eval a c5390 := h 5389 (by decide)
  have h5 : Entails.eval a c4170 := h 4169 (by decide)
  have h6 : Entails.eval a c4658 := h 4657 (by decide)
  have h7 : Entails.eval a c4349 := h 4348 (by decide)
  have h8 : Entails.eval a c4393 := h 4392 (by decide)
  have h9 : Entails.eval a c6154 := derived6154 a h
  have h10 : Entails.eval a c4411 := h 4410 (by decide)
  have h11 : Entails.eval a c3759 := h 3758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6156 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6094, some c5390, some c6140, some c4170, some c4831, some c4888, some c6081, some c4964, some c3688, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6156 : lratChecker f6156 p6156 = .success := by decide +kernel
theorem unsat6156 : Unsatisfiable (PosFin 65) f6156 := by
  apply lratCheckerSound f6156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6156
  · intro a ha; simp [p6156] at ha; subst a; trivial
  · exact checked6156
theorem derived6156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6156 := by
  apply localUnsat_implies_entails f6156 [c6094, c5390, c6140, c4170, c4831, c4888, c6081, c4964, c3688] c6156 unsat6156 (by rfl) a
  have h0 : Entails.eval a c6094 := derived6094 a h
  have h1 : Entails.eval a c5390 := h 5389 (by decide)
  have h2 : Entails.eval a c6140 := derived6140 a h
  have h3 : Entails.eval a c4170 := h 4169 (by decide)
  have h4 : Entails.eval a c4831 := h 4830 (by decide)
  have h5 : Entails.eval a c4888 := h 4887 (by decide)
  have h6 : Entails.eval a c6081 := derived6081 a h
  have h7 : Entails.eval a c4964 := h 4963 (by decide)
  have h8 : Entails.eval a c3688 := h 3687 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6157 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6153, some c6155, some c6094, some c6156, some c3652, some c5152, some c4888, some c4807, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6157 : lratChecker f6157 p6157 = .success := by decide +kernel
theorem unsat6157 : Unsatisfiable (PosFin 65) f6157 := by
  apply lratCheckerSound f6157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6157
  · intro a ha; simp [p6157] at ha; subst a; trivial
  · exact checked6157
theorem derived6157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6157 := by
  apply localUnsat_implies_entails f6157 [c6153, c6155, c6094, c6156, c3652, c5152, c4888, c4807] c6157 unsat6157 (by rfl) a
  have h0 : Entails.eval a c6153 := derived6153 a h
  have h1 : Entails.eval a c6155 := derived6155 a h
  have h2 : Entails.eval a c6094 := derived6094 a h
  have h3 : Entails.eval a c6156 := derived6156 a h
  have h4 : Entails.eval a c3652 := h 3651 (by decide)
  have h5 : Entails.eval a c5152 := h 5151 (by decide)
  have h6 : Entails.eval a c4888 := h 4887 (by decide)
  have h7 : Entails.eval a c4807 := h 4806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6158 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6153, some c6157, some c6062, some c6094, some c3652, some c5152, some c4807, some c4422, some c3988, some c4170, some c6086, some c4588, some c4196, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6158 : lratChecker f6158 p6158 = .success := by decide +kernel
theorem unsat6158 : Unsatisfiable (PosFin 65) f6158 := by
  apply lratCheckerSound f6158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6158
  · intro a ha; simp [p6158] at ha; subst a; trivial
  · exact checked6158
theorem derived6158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6158 := by
  apply localUnsat_implies_entails f6158 [c6153, c6157, c6062, c6094, c3652, c5152, c4807, c4422, c3988, c4170, c6086, c4588, c4196] c6158 unsat6158 (by rfl) a
  have h0 : Entails.eval a c6153 := derived6153 a h
  have h1 : Entails.eval a c6157 := derived6157 a h
  have h2 : Entails.eval a c6062 := derived6062 a h
  have h3 : Entails.eval a c6094 := derived6094 a h
  have h4 : Entails.eval a c3652 := h 3651 (by decide)
  have h5 : Entails.eval a c5152 := h 5151 (by decide)
  have h6 : Entails.eval a c4807 := h 4806 (by decide)
  have h7 : Entails.eval a c4422 := h 4421 (by decide)
  have h8 : Entails.eval a c3988 := h 3987 (by decide)
  have h9 : Entails.eval a c4170 := h 4169 (by decide)
  have h10 : Entails.eval a c6086 := derived6086 a h
  have h11 : Entails.eval a c4588 := h 4587 (by decide)
  have h12 : Entails.eval a c4196 := h 4195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6159 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c6094, some c5152, some c4807, some c3988, some c4170, some c5368, some c4528, some c6086, some c4588, some c4196, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6159 : lratChecker f6159 p6159 = .success := by decide +kernel
theorem unsat6159 : Unsatisfiable (PosFin 65) f6159 := by
  apply lratCheckerSound f6159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6159
  · intro a ha; simp [p6159] at ha; subst a; trivial
  · exact checked6159
theorem derived6159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6159 := by
  apply localUnsat_implies_entails f6159 [c6062, c6094, c5152, c4807, c3988, c4170, c5368, c4528, c6086, c4588, c4196] c6159 unsat6159 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c6094 := derived6094 a h
  have h2 : Entails.eval a c5152 := h 5151 (by decide)
  have h3 : Entails.eval a c4807 := h 4806 (by decide)
  have h4 : Entails.eval a c3988 := h 3987 (by decide)
  have h5 : Entails.eval a c4170 := h 4169 (by decide)
  have h6 : Entails.eval a c5368 := h 5367 (by decide)
  have h7 : Entails.eval a c4528 := h 4527 (by decide)
  have h8 : Entails.eval a c6086 := derived6086 a h
  have h9 : Entails.eval a c4588 := h 4587 (by decide)
  have h10 : Entails.eval a c4196 := h 4195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6160 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨41, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c6094, some c4170, some c5368, some c4528, some c6086, some c4588, some c4196, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6160 : lratChecker f6160 p6160 = .success := by decide +kernel
theorem unsat6160 : Unsatisfiable (PosFin 65) f6160 := by
  apply lratCheckerSound f6160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6160
  · intro a ha; simp [p6160] at ha; subst a; trivial
  · exact checked6160
theorem derived6160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6160 := by
  apply localUnsat_implies_entails f6160 [c6062, c6094, c4170, c5368, c4528, c6086, c4588, c4196] c6160 unsat6160 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c6094 := derived6094 a h
  have h2 : Entails.eval a c4170 := h 4169 (by decide)
  have h3 : Entails.eval a c5368 := h 5367 (by decide)
  have h4 : Entails.eval a c4528 := h 4527 (by decide)
  have h5 : Entails.eval a c6086 := derived6086 a h
  have h6 : Entails.eval a c4588 := h 4587 (by decide)
  have h7 : Entails.eval a c4196 := h 4195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6161 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4964, some c3688, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6161 : lratChecker f6161 p6161 = .success := by decide +kernel
theorem unsat6161 : Unsatisfiable (PosFin 65) f6161 := by
  apply lratCheckerSound f6161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6161
  · intro a ha; simp [p6161] at ha; subst a; trivial
  · exact checked6161
theorem derived6161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6161 := by
  apply localUnsat_implies_entails f6161 [c4964, c3688] c6161 unsat6161 (by rfl) a
  have h0 : Entails.eval a c4964 := h 4963 (by decide)
  have h1 : Entails.eval a c3688 := h 3687 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6162 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨61, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6062, some c4273, some c6160, some c5129, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6162 : lratChecker f6162 p6162 = .success := by decide +kernel
theorem unsat6162 : Unsatisfiable (PosFin 65) f6162 := by
  apply lratCheckerSound f6162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6162
  · intro a ha; simp [p6162] at ha; subst a; trivial
  · exact checked6162
theorem derived6162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6162 := by
  apply localUnsat_implies_entails f6162 [c6062, c4273, c6160, c5129] c6162 unsat6162 (by rfl) a
  have h0 : Entails.eval a c6062 := derived6062 a h
  have h1 : Entails.eval a c4273 := h 4272 (by decide)
  have h2 : Entails.eval a c6160 := derived6160 a h
  have h3 : Entails.eval a c5129 := h 5128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6163 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6153, some c6157, some c6062, some c6094, some c6158, some c6140, some c6161, some c3754, some c6162, some c4006, some c4807, some c5129, some c6159, some c6081, some c6139, some c3679, some c3687, some c5547, some c3706, some c3721, some c3908, some c6144, some c6145, some c2749, some c2799, some c2825, some c3304, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked6163 : lratChecker f6163 p6163 = .success := by decide +kernel
theorem unsat6163 : Unsatisfiable (PosFin 65) f6163 := by
  apply lratCheckerSound f6163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6163
  · intro a ha; simp [p6163] at ha; subst a; trivial
  · exact checked6163
theorem derived6163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6163 := by
  apply localUnsat_implies_entails f6163 [c6153, c6157, c6062, c6094, c6158, c6140, c6161, c3754, c6162, c4006, c4807, c5129, c6159, c6081, c6139, c3679, c3687, c5547, c3706, c3721, c3908, c6144, c6145, c2749, c2799, c2825, c3304] c6163 unsat6163 (by rfl) a
  have h0 : Entails.eval a c6153 := derived6153 a h
  have h1 : Entails.eval a c6157 := derived6157 a h
  have h2 : Entails.eval a c6062 := derived6062 a h
  have h3 : Entails.eval a c6094 := derived6094 a h
  have h4 : Entails.eval a c6158 := derived6158 a h
  have h5 : Entails.eval a c6140 := derived6140 a h
  have h6 : Entails.eval a c6161 := derived6161 a h
  have h7 : Entails.eval a c3754 := h 3753 (by decide)
  have h8 : Entails.eval a c6162 := derived6162 a h
  have h9 : Entails.eval a c4006 := h 4005 (by decide)
  have h10 : Entails.eval a c4807 := h 4806 (by decide)
  have h11 : Entails.eval a c5129 := h 5128 (by decide)
  have h12 : Entails.eval a c6159 := derived6159 a h
  have h13 : Entails.eval a c6081 := derived6081 a h
  have h14 : Entails.eval a c6139 := derived6139 a h
  have h15 : Entails.eval a c3679 := h 3678 (by decide)
  have h16 : Entails.eval a c3687 := h 3686 (by decide)
  have h17 : Entails.eval a c5547 := h 5546 (by decide)
  have h18 : Entails.eval a c3706 := h 3705 (by decide)
  have h19 : Entails.eval a c3721 := h 3720 (by decide)
  have h20 : Entails.eval a c3908 := h 3907 (by decide)
  have h21 : Entails.eval a c6144 := derived6144 a h
  have h22 : Entails.eval a c6145 := derived6145 a h
  have h23 : Entails.eval a c2749 := h 2748 (by decide)
  have h24 : Entails.eval a c2799 := h 2798 (by decide)
  have h25 : Entails.eval a c2825 := h 2824 (by decide)
  have h26 : Entails.eval a c3304 := h 3303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6164 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6153, some c6157, some c6062, some c6094, some c6158, some c6140, some c6159, some c6161, some c3754, some c6162, some c6081, some c4006, some c4807, some c6163, some c4957, some c4116, some c5012, some c4115, some c3909, some c4963, some c6144, some c6145, some c2749, some c2799, some c2825, some c3304, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked6164 : lratChecker f6164 p6164 = .success := by decide +kernel
theorem unsat6164 : Unsatisfiable (PosFin 65) f6164 := by
  apply lratCheckerSound f6164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6164
  · intro a ha; simp [p6164] at ha; subst a; trivial
  · exact checked6164
theorem derived6164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6164 := by
  apply localUnsat_implies_entails f6164 [c6139, c6153, c6157, c6062, c6094, c6158, c6140, c6159, c6161, c3754, c6162, c6081, c4006, c4807, c6163, c4957, c4116, c5012, c4115, c3909, c4963, c6144, c6145, c2749, c2799, c2825, c3304] c6164 unsat6164 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6153 := derived6153 a h
  have h2 : Entails.eval a c6157 := derived6157 a h
  have h3 : Entails.eval a c6062 := derived6062 a h
  have h4 : Entails.eval a c6094 := derived6094 a h
  have h5 : Entails.eval a c6158 := derived6158 a h
  have h6 : Entails.eval a c6140 := derived6140 a h
  have h7 : Entails.eval a c6159 := derived6159 a h
  have h8 : Entails.eval a c6161 := derived6161 a h
  have h9 : Entails.eval a c3754 := h 3753 (by decide)
  have h10 : Entails.eval a c6162 := derived6162 a h
  have h11 : Entails.eval a c6081 := derived6081 a h
  have h12 : Entails.eval a c4006 := h 4005 (by decide)
  have h13 : Entails.eval a c4807 := h 4806 (by decide)
  have h14 : Entails.eval a c6163 := derived6163 a h
  have h15 : Entails.eval a c4957 := h 4956 (by decide)
  have h16 : Entails.eval a c4116 := h 4115 (by decide)
  have h17 : Entails.eval a c5012 := h 5011 (by decide)
  have h18 : Entails.eval a c4115 := h 4114 (by decide)
  have h19 : Entails.eval a c3909 := h 3908 (by decide)
  have h20 : Entails.eval a c4963 := h 4962 (by decide)
  have h21 : Entails.eval a c6144 := derived6144 a h
  have h22 : Entails.eval a c6145 := derived6145 a h
  have h23 : Entails.eval a c2749 := h 2748 (by decide)
  have h24 : Entails.eval a c2799 := h 2798 (by decide)
  have h25 : Entails.eval a c2825 := h 2824 (by decide)
  have h26 : Entails.eval a c3304 := h 3303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6165 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5273, some c4116, some c5012, some c4115, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6165 : lratChecker f6165 p6165 = .success := by decide +kernel
theorem unsat6165 : Unsatisfiable (PosFin 65) f6165 := by
  apply lratCheckerSound f6165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6165
  · intro a ha; simp [p6165] at ha; subst a; trivial
  · exact checked6165
theorem derived6165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6165 := by
  apply localUnsat_implies_entails f6165 [c5273, c4116, c5012, c4115] c6165 unsat6165 (by rfl) a
  have h0 : Entails.eval a c5273 := h 5272 (by decide)
  have h1 : Entails.eval a c4116 := h 4115 (by decide)
  have h2 : Entails.eval a c5012 := h 5011 (by decide)
  have h3 : Entails.eval a c4115 := h 4114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6166 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6094, some c6140, some c6161, some c3754, some c6156, some c6164, some c6139, some c4006, some c4807, some c4831, some c4226, some c5129, some c6165, some c3679, some c3687, some c5547, some c3706, some c3678, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6166 : lratChecker f6166 p6166 = .success := by decide +kernel
theorem unsat6166 : Unsatisfiable (PosFin 65) f6166 := by
  apply lratCheckerSound f6166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6166
  · intro a ha; simp [p6166] at ha; subst a; trivial
  · exact checked6166
theorem derived6166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6166 := by
  apply localUnsat_implies_entails f6166 [c6094, c6140, c6161, c3754, c6156, c6164, c6139, c4006, c4807, c4831, c4226, c5129, c6165, c3679, c3687, c5547, c3706, c3678] c6166 unsat6166 (by rfl) a
  have h0 : Entails.eval a c6094 := derived6094 a h
  have h1 : Entails.eval a c6140 := derived6140 a h
  have h2 : Entails.eval a c6161 := derived6161 a h
  have h3 : Entails.eval a c3754 := h 3753 (by decide)
  have h4 : Entails.eval a c6156 := derived6156 a h
  have h5 : Entails.eval a c6164 := derived6164 a h
  have h6 : Entails.eval a c6139 := derived6139 a h
  have h7 : Entails.eval a c4006 := h 4005 (by decide)
  have h8 : Entails.eval a c4807 := h 4806 (by decide)
  have h9 : Entails.eval a c4831 := h 4830 (by decide)
  have h10 : Entails.eval a c4226 := h 4225 (by decide)
  have h11 : Entails.eval a c5129 := h 5128 (by decide)
  have h12 : Entails.eval a c6165 := derived6165 a h
  have h13 : Entails.eval a c3679 := h 3678 (by decide)
  have h14 : Entails.eval a c3687 := h 3686 (by decide)
  have h15 : Entails.eval a c5547 := h 5546 (by decide)
  have h16 : Entails.eval a c3706 := h 3705 (by decide)
  have h17 : Entails.eval a c3678 := h 3677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6167 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6094, some c6156, some c6140, some c6161, some c3754, some c5434, some c6166, some c4273, some c5129, some c5890, some c5560, some c6005, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6167 : lratChecker f6167 p6167 = .success := by decide +kernel
theorem unsat6167 : Unsatisfiable (PosFin 65) f6167 := by
  apply lratCheckerSound f6167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6167
  · intro a ha; simp [p6167] at ha; subst a; trivial
  · exact checked6167
theorem derived6167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6167 := by
  apply localUnsat_implies_entails f6167 [c6094, c6156, c6140, c6161, c3754, c5434, c6166, c4273, c5129, c5890, c5560, c6005] c6167 unsat6167 (by rfl) a
  have h0 : Entails.eval a c6094 := derived6094 a h
  have h1 : Entails.eval a c6156 := derived6156 a h
  have h2 : Entails.eval a c6140 := derived6140 a h
  have h3 : Entails.eval a c6161 := derived6161 a h
  have h4 : Entails.eval a c3754 := h 3753 (by decide)
  have h5 : Entails.eval a c5434 := h 5433 (by decide)
  have h6 : Entails.eval a c6166 := derived6166 a h
  have h7 : Entails.eval a c4273 := h 4272 (by decide)
  have h8 : Entails.eval a c5129 := h 5128 (by decide)
  have h9 : Entails.eval a c5890 := derived5890 a h
  have h10 : Entails.eval a c5560 := h 5559 (by decide)
  have h11 : Entails.eval a c6005 := derived6005 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6168 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨61, by decide⟩, false), (⟨33, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3622, some c5450, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6168 : lratChecker f6168 p6168 = .success := by decide +kernel
theorem unsat6168 : Unsatisfiable (PosFin 65) f6168 := by
  apply lratCheckerSound f6168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6168
  · intro a ha; simp [p6168] at ha; subst a; trivial
  · exact checked6168
theorem derived6168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6168 := by
  apply localUnsat_implies_entails f6168 [c3622, c5450] c6168 unsat6168 (by rfl) a
  have h0 : Entails.eval a c3622 := h 3621 (by decide)
  have h1 : Entails.eval a c5450 := h 5449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6169 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6164, some c6167, some c6062, some c6067, some c5336, some c5390, some c4170, some c4658, some c5793, some c4349, some c4393, some c6168, some c6068, some c6008, some c6070, some c4125, some c3696, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6169 : lratChecker f6169 p6169 = .success := by decide +kernel
theorem unsat6169 : Unsatisfiable (PosFin 65) f6169 := by
  apply lratCheckerSound f6169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6169
  · intro a ha; simp [p6169] at ha; subst a; trivial
  · exact checked6169
theorem derived6169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6169 := by
  apply localUnsat_implies_entails f6169 [c6164, c6167, c6062, c6067, c5336, c5390, c4170, c4658, c5793, c4349, c4393, c6168, c6068, c6008, c6070, c4125, c3696] c6169 unsat6169 (by rfl) a
  have h0 : Entails.eval a c6164 := derived6164 a h
  have h1 : Entails.eval a c6167 := derived6167 a h
  have h2 : Entails.eval a c6062 := derived6062 a h
  have h3 : Entails.eval a c6067 := derived6067 a h
  have h4 : Entails.eval a c5336 := h 5335 (by decide)
  have h5 : Entails.eval a c5390 := h 5389 (by decide)
  have h6 : Entails.eval a c4170 := h 4169 (by decide)
  have h7 : Entails.eval a c4658 := h 4657 (by decide)
  have h8 : Entails.eval a c5793 := h 5792 (by decide)
  have h9 : Entails.eval a c4349 := h 4348 (by decide)
  have h10 : Entails.eval a c4393 := h 4392 (by decide)
  have h11 : Entails.eval a c6168 := derived6168 a h
  have h12 : Entails.eval a c6068 := derived6068 a h
  have h13 : Entails.eval a c6008 := derived6008 a h
  have h14 : Entails.eval a c6070 := derived6070 a h
  have h15 : Entails.eval a c4125 := h 4124 (by decide)
  have h16 : Entails.eval a c3696 := h 3695 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6170 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, true), (⟨38, by decide⟩, true), (⟨55, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4363, some c5346, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p6170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6170 : lratChecker f6170 p6170 = .success := by decide +kernel
theorem unsat6170 : Unsatisfiable (PosFin 65) f6170 := by
  apply lratCheckerSound f6170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6170
  · intro a ha; simp [p6170] at ha; subst a; trivial
  · exact checked6170
theorem derived6170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6170 := by
  apply localUnsat_implies_entails f6170 [c4363, c5346] c6170 unsat6170 (by rfl) a
  have h0 : Entails.eval a c4363 := h 4362 (by decide)
  have h1 : Entails.eval a c5346 := h 5345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6171 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6169, some c3652, some c6067, some c5152, some c6094, some c4807, some c4422, some c3988, some c4170, some c6170, some c3660, some c4581, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6171 : lratChecker f6171 p6171 = .success := by decide +kernel
theorem unsat6171 : Unsatisfiable (PosFin 65) f6171 := by
  apply lratCheckerSound f6171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6171
  · intro a ha; simp [p6171] at ha; subst a; trivial
  · exact checked6171
theorem derived6171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6171 := by
  apply localUnsat_implies_entails f6171 [c6139, c6169, c3652, c6067, c5152, c6094, c4807, c4422, c3988, c4170, c6170, c3660, c4581] c6171 unsat6171 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6169 := derived6169 a h
  have h2 : Entails.eval a c3652 := h 3651 (by decide)
  have h3 : Entails.eval a c6067 := derived6067 a h
  have h4 : Entails.eval a c5152 := h 5151 (by decide)
  have h5 : Entails.eval a c6094 := derived6094 a h
  have h6 : Entails.eval a c4807 := h 4806 (by decide)
  have h7 : Entails.eval a c4422 := h 4421 (by decide)
  have h8 : Entails.eval a c3988 := h 3987 (by decide)
  have h9 : Entails.eval a c4170 := h 4169 (by decide)
  have h10 : Entails.eval a c6170 := derived6170 a h
  have h11 : Entails.eval a c3660 := h 3659 (by decide)
  have h12 : Entails.eval a c4581 := h 4580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6172 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨62, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4911, some c5252, some c4657, some c4685, some c4591, some c4294, some c3943, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6172 : lratChecker f6172 p6172 = .success := by decide +kernel
theorem unsat6172 : Unsatisfiable (PosFin 65) f6172 := by
  apply lratCheckerSound f6172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6172
  · intro a ha; simp [p6172] at ha; subst a; trivial
  · exact checked6172
theorem derived6172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6172 := by
  apply localUnsat_implies_entails f6172 [c4911, c5252, c4657, c4685, c4591, c4294, c3943] c6172 unsat6172 (by rfl) a
  have h0 : Entails.eval a c4911 := h 4910 (by decide)
  have h1 : Entails.eval a c5252 := h 5251 (by decide)
  have h2 : Entails.eval a c4657 := h 4656 (by decide)
  have h3 : Entails.eval a c4685 := h 4684 (by decide)
  have h4 : Entails.eval a c4591 := h 4590 (by decide)
  have h5 : Entails.eval a c4294 := h 4293 (by decide)
  have h6 : Entails.eval a c3943 := h 3942 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6173 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨62, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3674, some c3651, some c6172, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6173 : lratChecker f6173 p6173 = .success := by decide +kernel
theorem unsat6173 : Unsatisfiable (PosFin 65) f6173 := by
  apply lratCheckerSound f6173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6173
  · intro a ha; simp [p6173] at ha; subst a; trivial
  · exact checked6173
theorem derived6173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6173 := by
  apply localUnsat_implies_entails f6173 [c3674, c3651, c6172] c6173 unsat6173 (by rfl) a
  have h0 : Entails.eval a c3674 := h 3673 (by decide)
  have h1 : Entails.eval a c3651 := h 3650 (by decide)
  have h2 : Entails.eval a c6172 := derived6172 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6174 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, true), (⟨40, by decide⟩, false), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4052, some c4500, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p6174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6174 : lratChecker f6174 p6174 = .success := by decide +kernel
theorem unsat6174 : Unsatisfiable (PosFin 65) f6174 := by
  apply lratCheckerSound f6174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6174
  · intro a ha; simp [p6174] at ha; subst a; trivial
  · exact checked6174
theorem derived6174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6174 := by
  apply localUnsat_implies_entails f6174 [c4052, c4500] c6174 unsat6174 (by rfl) a
  have h0 : Entails.eval a c4052 := h 4051 (by decide)
  have h1 : Entails.eval a c4500 := h 4499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6175 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6171, some c6139, some c6173, some c6164, some c6172, some c3792, some c4991, some c5703, some c3628, some c4685, some c4392, some c4008, some c6174, some c3590, some c5717, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6175 : lratChecker f6175 p6175 = .success := by decide +kernel
theorem unsat6175 : Unsatisfiable (PosFin 65) f6175 := by
  apply lratCheckerSound f6175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6175
  · intro a ha; simp [p6175] at ha; subst a; trivial
  · exact checked6175
theorem derived6175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6175 := by
  apply localUnsat_implies_entails f6175 [c6171, c6139, c6173, c6164, c6172, c3792, c4991, c5703, c3628, c4685, c4392, c4008, c6174, c3590, c5717] c6175 unsat6175 (by rfl) a
  have h0 : Entails.eval a c6171 := derived6171 a h
  have h1 : Entails.eval a c6139 := derived6139 a h
  have h2 : Entails.eval a c6173 := derived6173 a h
  have h3 : Entails.eval a c6164 := derived6164 a h
  have h4 : Entails.eval a c6172 := derived6172 a h
  have h5 : Entails.eval a c3792 := h 3791 (by decide)
  have h6 : Entails.eval a c4991 := h 4990 (by decide)
  have h7 : Entails.eval a c5703 := h 5702 (by decide)
  have h8 : Entails.eval a c3628 := h 3627 (by decide)
  have h9 : Entails.eval a c4685 := h 4684 (by decide)
  have h10 : Entails.eval a c4392 := h 4391 (by decide)
  have h11 : Entails.eval a c4008 := h 4007 (by decide)
  have h12 : Entails.eval a c6174 := derived6174 a h
  have h13 : Entails.eval a c3590 := h 3589 (by decide)
  have h14 : Entails.eval a c5717 := h 5716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6176 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, false), (⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6173, some c5435, some c4991, some c4685, some c4392, some c4008, some c6174, some c3590, some c5450, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6176 : lratChecker f6176 p6176 = .success := by decide +kernel
theorem unsat6176 : Unsatisfiable (PosFin 65) f6176 := by
  apply lratCheckerSound f6176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6176
  · intro a ha; simp [p6176] at ha; subst a; trivial
  · exact checked6176
theorem derived6176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6176 := by
  apply localUnsat_implies_entails f6176 [c6173, c5435, c4991, c4685, c4392, c4008, c6174, c3590, c5450] c6176 unsat6176 (by rfl) a
  have h0 : Entails.eval a c6173 := derived6173 a h
  have h1 : Entails.eval a c5435 := h 5434 (by decide)
  have h2 : Entails.eval a c4991 := h 4990 (by decide)
  have h3 : Entails.eval a c4685 := h 4684 (by decide)
  have h4 : Entails.eval a c4392 := h 4391 (by decide)
  have h5 : Entails.eval a c4008 := h 4007 (by decide)
  have h6 : Entails.eval a c6174 := derived6174 a h
  have h7 : Entails.eval a c3590 := h 3589 (by decide)
  have h8 : Entails.eval a c5450 := h 5449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6177 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨58, by decide⟩, false), (⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨61, by decide⟩, false), (⟨62, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6148, some c5919, some c5838, some c5837, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6177 : lratChecker f6177 p6177 = .success := by decide +kernel
theorem unsat6177 : Unsatisfiable (PosFin 65) f6177 := by
  apply lratCheckerSound f6177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6177
  · intro a ha; simp [p6177] at ha; subst a; trivial
  · exact checked6177
theorem derived6177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6177 := by
  apply localUnsat_implies_entails f6177 [c6148, c5919, c5838, c5837] c6177 unsat6177 (by rfl) a
  have h0 : Entails.eval a c6148 := derived6148 a h
  have h1 : Entails.eval a c5919 := derived5919 a h
  have h2 : Entails.eval a c5838 := h 5837 (by decide)
  have h3 : Entails.eval a c5837 := h 5836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6178 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨59, by decide⟩, true), (⟨63, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6139, some c6164, some c6171, some c6173, some c6175, some c3905, some c5435, some c6176, some c3792, some c4951, some c4685, some c4830, some c4847, some c6140, some c4591, some c5446, some c6161, some c6177, some c6165, some c3679, some c3693, some c4735, some c4467, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked6178 : lratChecker f6178 p6178 = .success := by decide +kernel
theorem unsat6178 : Unsatisfiable (PosFin 65) f6178 := by
  apply lratCheckerSound f6178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6178
  · intro a ha; simp [p6178] at ha; subst a; trivial
  · exact checked6178
theorem derived6178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6178 := by
  apply localUnsat_implies_entails f6178 [c6139, c6164, c6171, c6173, c6175, c3905, c5435, c6176, c3792, c4951, c4685, c4830, c4847, c6140, c4591, c5446, c6161, c6177, c6165, c3679, c3693, c4735, c4467] c6178 unsat6178 (by rfl) a
  have h0 : Entails.eval a c6139 := derived6139 a h
  have h1 : Entails.eval a c6164 := derived6164 a h
  have h2 : Entails.eval a c6171 := derived6171 a h
  have h3 : Entails.eval a c6173 := derived6173 a h
  have h4 : Entails.eval a c6175 := derived6175 a h
  have h5 : Entails.eval a c3905 := h 3904 (by decide)
  have h6 : Entails.eval a c5435 := h 5434 (by decide)
  have h7 : Entails.eval a c6176 := derived6176 a h
  have h8 : Entails.eval a c3792 := h 3791 (by decide)
  have h9 : Entails.eval a c4951 := h 4950 (by decide)
  have h10 : Entails.eval a c4685 := h 4684 (by decide)
  have h11 : Entails.eval a c4830 := h 4829 (by decide)
  have h12 : Entails.eval a c4847 := h 4846 (by decide)
  have h13 : Entails.eval a c6140 := derived6140 a h
  have h14 : Entails.eval a c4591 := h 4590 (by decide)
  have h15 : Entails.eval a c5446 := h 5445 (by decide)
  have h16 : Entails.eval a c6161 := derived6161 a h
  have h17 : Entails.eval a c6177 := derived6177 a h
  have h18 : Entails.eval a c6165 := derived6165 a h
  have h19 : Entails.eval a c3679 := h 3678 (by decide)
  have h20 : Entails.eval a c3693 := h 3692 (by decide)
  have h21 : Entails.eval a c4735 := h 4734 (by decide)
  have h22 : Entails.eval a c4467 := h 4466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6179 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4830, some c4806, some c3817, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6179 : lratChecker f6179 p6179 = .success := by decide +kernel
theorem unsat6179 : Unsatisfiable (PosFin 65) f6179 := by
  apply lratCheckerSound f6179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6179
  · intro a ha; simp [p6179] at ha; subst a; trivial
  · exact checked6179
theorem derived6179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6179 := by
  apply localUnsat_implies_entails f6179 [c4830, c4806, c3817] c6179 unsat6179 (by rfl) a
  have h0 : Entails.eval a c4830 := h 4829 (by decide)
  have h1 : Entails.eval a c4806 := h 4805 (by decide)
  have h2 : Entails.eval a c3817 := h 3816 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6180 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨59, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6172, some c3522, some c4951, some c4639, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6180 : lratChecker f6180 p6180 = .success := by decide +kernel
theorem unsat6180 : Unsatisfiable (PosFin 65) f6180 := by
  apply lratCheckerSound f6180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6180
  · intro a ha; simp [p6180] at ha; subst a; trivial
  · exact checked6180
theorem derived6180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6180 := by
  apply localUnsat_implies_entails f6180 [c6172, c3522, c4951, c4639] c6180 unsat6180 (by rfl) a
  have h0 : Entails.eval a c6172 := derived6172 a h
  have h1 : Entails.eval a c3522 := h 3521 (by decide)
  have h2 : Entails.eval a c4951 := h 4950 (by decide)
  have h3 : Entails.eval a c4639 := h 4638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived6180

end CochromaticTwenty.Certificates.FixedCore1
