import MerLeanExperiment.Certificates.FixedCore1.Steps3100_3199

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9081 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5343, some c4210, some c4426, some c5398, some c4477, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9081 : lratChecker f9081 p9081 = .success := by decide +kernel
theorem unsat9081 : Unsatisfiable (PosFin 65) f9081 := by
  apply lratCheckerSound f9081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9081
  · intro a ha; simp [p9081] at ha; subst a; trivial
  · exact checked9081
theorem derived9081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9081 := by
  apply localUnsat_implies_entails f9081 [c5343, c4210, c4426, c5398, c4477] c9081 unsat9081 (by rfl) a
  have h0 : Entails.eval a c5343 := h 5342 (by decide)
  have h1 : Entails.eval a c4210 := h 4209 (by decide)
  have h2 : Entails.eval a c4426 := h 4425 (by decide)
  have h3 : Entails.eval a c5398 := h 5397 (by decide)
  have h4 : Entails.eval a c4477 := h 4476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9082 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5258, some c5766, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p9082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9082 : lratChecker f9082 p9082 = .success := by decide +kernel
theorem unsat9082 : Unsatisfiable (PosFin 65) f9082 := by
  apply lratCheckerSound f9082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9082
  · intro a ha; simp [p9082] at ha; subst a; trivial
  · exact checked9082
theorem derived9082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9082 := by
  apply localUnsat_implies_entails f9082 [c5258, c5766] c9082 unsat9082 (by rfl) a
  have h0 : Entails.eval a c5258 := h 5257 (by decide)
  have h1 : Entails.eval a c5766 := h 5765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9083 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5858, some c5297, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9083 : lratChecker f9083 p9083 = .success := by decide +kernel
theorem unsat9083 : Unsatisfiable (PosFin 65) f9083 := by
  apply lratCheckerSound f9083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9083
  · intro a ha; simp [p9083] at ha; subst a; trivial
  · exact checked9083
theorem derived9083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9083 := by
  apply localUnsat_implies_entails f9083 [c5858, c5297] c9083 unsat9083 (by rfl) a
  have h0 : Entails.eval a c5858 := h 5857 (by decide)
  have h1 : Entails.eval a c5297 := h 5296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9084 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨45, by decide⟩, true), (⟨51, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c5530, some c9066, some c9082, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9084 : lratChecker f9084 p9084 = .success := by decide +kernel
theorem unsat9084 : Unsatisfiable (PosFin 65) f9084 := by
  apply lratCheckerSound f9084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9084
  · intro a ha; simp [p9084] at ha; subst a; trivial
  · exact checked9084
theorem derived9084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9084 := by
  apply localUnsat_implies_entails f9084 [c7129, c5530, c9066, c9082] c9084 unsat9084 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c5530 := h 5529 (by decide)
  have h2 : Entails.eval a c9066 := derived9066 a h
  have h3 : Entails.eval a c9082 := derived9082 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9085 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨51, by decide⟩, true), (⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c4979, some c9080, some c9084, some c4477, some c4460, some c4402, some c5281, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9085 : lratChecker f9085 p9085 = .success := by decide +kernel
theorem unsat9085 : Unsatisfiable (PosFin 65) f9085 := by
  apply lratCheckerSound f9085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9085
  · intro a ha; simp [p9085] at ha; subst a; trivial
  · exact checked9085
theorem derived9085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9085 := by
  apply localUnsat_implies_entails f9085 [c7129, c4979, c9080, c9084, c4477, c4460, c4402, c5281] c9085 unsat9085 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c4979 := h 4978 (by decide)
  have h2 : Entails.eval a c9080 := derived9080 a h
  have h3 : Entails.eval a c9084 := derived9084 a h
  have h4 : Entails.eval a c4477 := h 4476 (by decide)
  have h5 : Entails.eval a c4460 := h 4459 (by decide)
  have h6 : Entails.eval a c4402 := h 4401 (by decide)
  have h7 : Entails.eval a c5281 := h 5280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9086 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨59, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2879, some c2886, some c3338, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p9086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9086 : lratChecker f9086 p9086 = .success := by decide +kernel
theorem unsat9086 : Unsatisfiable (PosFin 65) f9086 := by
  apply lratCheckerSound f9086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9086
  · intro a ha; simp [p9086] at ha; subst a; trivial
  · exact checked9086
theorem derived9086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9086 := by
  apply localUnsat_implies_entails f9086 [c2879, c2886, c3338] c9086 unsat9086 (by rfl) a
  have h0 : Entails.eval a c2879 := h 2878 (by decide)
  have h1 : Entails.eval a c2886 := h 2885 (by decide)
  have h2 : Entails.eval a c3338 := h 3337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9087 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨61, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3385, some c3381, some c3378, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p9087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9087 : lratChecker f9087 p9087 = .success := by decide +kernel
theorem unsat9087 : Unsatisfiable (PosFin 65) f9087 := by
  apply lratCheckerSound f9087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9087
  · intro a ha; simp [p9087] at ha; subst a; trivial
  · exact checked9087
theorem derived9087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9087 := by
  apply localUnsat_implies_entails f9087 [c3385, c3381, c3378] c9087 unsat9087 (by rfl) a
  have h0 : Entails.eval a c3385 := h 3384 (by decide)
  have h1 : Entails.eval a c3381 := h 3380 (by decide)
  have h2 : Entails.eval a c3378 := h 3377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9088 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨63, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6312, some c9086, some c9087, some c3075, some c3286, some c3356, some c3049, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p9088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9088 : lratChecker f9088 p9088 = .success := by decide +kernel
theorem unsat9088 : Unsatisfiable (PosFin 65) f9088 := by
  apply lratCheckerSound f9088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9088
  · intro a ha; simp [p9088] at ha; subst a; trivial
  · exact checked9088
theorem derived9088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9088 := by
  apply localUnsat_implies_entails f9088 [c6312, c9086, c9087, c3075, c3286, c3356, c3049] c9088 unsat9088 (by rfl) a
  have h0 : Entails.eval a c6312 := derived6312 a h
  have h1 : Entails.eval a c9086 := derived9086 a h
  have h2 : Entails.eval a c9087 := derived9087 a h
  have h3 : Entails.eval a c3075 := h 3074 (by decide)
  have h4 : Entails.eval a c3286 := h 3285 (by decide)
  have h5 : Entails.eval a c3356 := h 3355 (by decide)
  have h6 : Entails.eval a c3049 := h 3048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9089 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9085, some c3973, some c4979, some c4643, some c4477, some c4402, some c3480, some c5685, some c5363, some c5686, some c5676, some c4289, some c3855, some c6862, some c9088, some c2857, some c2780, some c3084, some c3082, some c3266, some c3359, some c3212, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9089 : lratChecker f9089 p9089 = .success := by decide +kernel
theorem unsat9089 : Unsatisfiable (PosFin 65) f9089 := by
  apply lratCheckerSound f9089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9089
  · intro a ha; simp [p9089] at ha; subst a; trivial
  · exact checked9089
theorem derived9089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9089 := by
  apply localUnsat_implies_entails f9089 [c7129, c9085, c3973, c4979, c4643, c4477, c4402, c3480, c5685, c5363, c5686, c5676, c4289, c3855, c6862, c9088, c2857, c2780, c3084, c3082, c3266, c3359, c3212] c9089 unsat9089 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9085 := derived9085 a h
  have h2 : Entails.eval a c3973 := h 3972 (by decide)
  have h3 : Entails.eval a c4979 := h 4978 (by decide)
  have h4 : Entails.eval a c4643 := h 4642 (by decide)
  have h5 : Entails.eval a c4477 := h 4476 (by decide)
  have h6 : Entails.eval a c4402 := h 4401 (by decide)
  have h7 : Entails.eval a c3480 := h 3479 (by decide)
  have h8 : Entails.eval a c5685 := h 5684 (by decide)
  have h9 : Entails.eval a c5363 := h 5362 (by decide)
  have h10 : Entails.eval a c5686 := h 5685 (by decide)
  have h11 : Entails.eval a c5676 := h 5675 (by decide)
  have h12 : Entails.eval a c4289 := h 4288 (by decide)
  have h13 : Entails.eval a c3855 := h 3854 (by decide)
  have h14 : Entails.eval a c6862 := derived6862 a h
  have h15 : Entails.eval a c9088 := derived9088 a h
  have h16 : Entails.eval a c2857 := h 2856 (by decide)
  have h17 : Entails.eval a c2780 := h 2779 (by decide)
  have h18 : Entails.eval a c3084 := h 3083 (by decide)
  have h19 : Entails.eval a c3082 := h 3081 (by decide)
  have h20 : Entails.eval a c3266 := h 3265 (by decide)
  have h21 : Entails.eval a c3359 := h 3358 (by decide)
  have h22 : Entails.eval a c3212 := h 3211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9090 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨61, by decide⟩, false), (⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨50, by decide⟩, false), (⟨35, by decide⟩, true), (⟨41, by decide⟩, true), (⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2856, some c3086, some c3079, some c3263, some c3358, some c3215, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9090 : lratChecker f9090 p9090 = .success := by decide +kernel
theorem unsat9090 : Unsatisfiable (PosFin 65) f9090 := by
  apply lratCheckerSound f9090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9090
  · intro a ha; simp [p9090] at ha; subst a; trivial
  · exact checked9090
theorem derived9090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9090 := by
  apply localUnsat_implies_entails f9090 [c2856, c3086, c3079, c3263, c3358, c3215] c9090 unsat9090 (by rfl) a
  have h0 : Entails.eval a c2856 := h 2855 (by decide)
  have h1 : Entails.eval a c3086 := h 3085 (by decide)
  have h2 : Entails.eval a c3079 := h 3078 (by decide)
  have h3 : Entails.eval a c3263 := h 3262 (by decide)
  have h4 : Entails.eval a c3358 := h 3357 (by decide)
  have h5 : Entails.eval a c3215 := h 3214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9091 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨54, by decide⟩, false), (⟨63, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨41, by decide⟩, true), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2958, some c3162, some c3369, some c2919, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9091 : lratChecker f9091 p9091 = .success := by decide +kernel
theorem unsat9091 : Unsatisfiable (PosFin 65) f9091 := by
  apply lratCheckerSound f9091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9091
  · intro a ha; simp [p9091] at ha; subst a; trivial
  · exact checked9091
theorem derived9091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9091 := by
  apply localUnsat_implies_entails f9091 [c2958, c3162, c3369, c2919] c9091 unsat9091 (by rfl) a
  have h0 : Entails.eval a c2958 := h 2957 (by decide)
  have h1 : Entails.eval a c3162 := h 3161 (by decide)
  have h2 : Entails.eval a c3369 := h 3368 (by decide)
  have h3 : Entails.eval a c2919 := h 2918 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9092 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨63, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2692, some c2800, some c3006, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p9092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9092 : lratChecker f9092 p9092 = .success := by decide +kernel
theorem unsat9092 : Unsatisfiable (PosFin 65) f9092 := by
  apply lratCheckerSound f9092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9092
  · intro a ha; simp [p9092] at ha; subst a; trivial
  · exact checked9092
theorem derived9092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9092 := by
  apply localUnsat_implies_entails f9092 [c2692, c2800, c3006] c9092 unsat9092 (by rfl) a
  have h0 : Entails.eval a c2692 := h 2691 (by decide)
  have h1 : Entails.eval a c2800 := h 2799 (by decide)
  have h2 : Entails.eval a c3006 := h 3005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9093 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨54, by decide⟩, false), (⟨63, by decide⟩, false), (⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, true), (⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9091, some c9092, some c3339, some c3411, some c3317, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9093 : lratChecker f9093 p9093 = .success := by decide +kernel
theorem unsat9093 : Unsatisfiable (PosFin 65) f9093 := by
  apply lratCheckerSound f9093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9093
  · intro a ha; simp [p9093] at ha; subst a; trivial
  · exact checked9093
theorem derived9093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9093 := by
  apply localUnsat_implies_entails f9093 [c9091, c9092, c3339, c3411, c3317] c9093 unsat9093 (by rfl) a
  have h0 : Entails.eval a c9091 := derived9091 a h
  have h1 : Entails.eval a c9092 := derived9092 a h
  have h2 : Entails.eval a c3339 := h 3338 (by decide)
  have h3 : Entails.eval a c3411 := h 3410 (by decide)
  have h4 : Entails.eval a c3317 := h 3316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9094 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9079, some c9064, some c9081, some c4979, some c4477, some c4402, some c4133, some c9080, some c9083, some c9085, some c4210, some c3973, some c4643, some c9089, some c4443, some c5550, some c5868, some c6597, some c4385, some c9093, some c2780, some c9090, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9094 : lratChecker f9094 p9094 = .success := by decide +kernel
theorem unsat9094 : Unsatisfiable (PosFin 65) f9094 := by
  apply lratCheckerSound f9094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9094
  · intro a ha; simp [p9094] at ha; subst a; trivial
  · exact checked9094
theorem derived9094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9094 := by
  apply localUnsat_implies_entails f9094 [c7129, c9079, c9064, c9081, c4979, c4477, c4402, c4133, c9080, c9083, c9085, c4210, c3973, c4643, c9089, c4443, c5550, c5868, c6597, c4385, c9093, c2780, c9090] c9094 unsat9094 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c9081 := derived9081 a h
  have h4 : Entails.eval a c4979 := h 4978 (by decide)
  have h5 : Entails.eval a c4477 := h 4476 (by decide)
  have h6 : Entails.eval a c4402 := h 4401 (by decide)
  have h7 : Entails.eval a c4133 := h 4132 (by decide)
  have h8 : Entails.eval a c9080 := derived9080 a h
  have h9 : Entails.eval a c9083 := derived9083 a h
  have h10 : Entails.eval a c9085 := derived9085 a h
  have h11 : Entails.eval a c4210 := h 4209 (by decide)
  have h12 : Entails.eval a c3973 := h 3972 (by decide)
  have h13 : Entails.eval a c4643 := h 4642 (by decide)
  have h14 : Entails.eval a c9089 := derived9089 a h
  have h15 : Entails.eval a c4443 := h 4442 (by decide)
  have h16 : Entails.eval a c5550 := h 5549 (by decide)
  have h17 : Entails.eval a c5868 := h 5867 (by decide)
  have h18 : Entails.eval a c6597 := derived6597 a h
  have h19 : Entails.eval a c4385 := h 4384 (by decide)
  have h20 : Entails.eval a c9093 := derived9093 a h
  have h21 : Entails.eval a c2780 := h 2779 (by decide)
  have h22 : Entails.eval a c9090 := derived9090 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9095 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9064, some c9080, some c9079, some c9081, some c9083, some c9094, some c5672, some c5863, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9095 : lratChecker f9095 p9095 = .success := by decide +kernel
theorem unsat9095 : Unsatisfiable (PosFin 65) f9095 := by
  apply lratCheckerSound f9095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9095
  · intro a ha; simp [p9095] at ha; subst a; trivial
  · exact checked9095
theorem derived9095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9095 := by
  apply localUnsat_implies_entails f9095 [c7129, c9064, c9080, c9079, c9081, c9083, c9094, c5672, c5863] c9095 unsat9095 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c9080 := derived9080 a h
  have h3 : Entails.eval a c9079 := derived9079 a h
  have h4 : Entails.eval a c9081 := derived9081 a h
  have h5 : Entails.eval a c9083 := derived9083 a h
  have h6 : Entails.eval a c9094 := derived9094 a h
  have h7 : Entails.eval a c5672 := h 5671 (by decide)
  have h8 : Entails.eval a c5863 := h 5862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9096 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨47, by decide⟩, true), (⟨39, by decide⟩, false), (⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5258, some c5156, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p9096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9096 : lratChecker f9096 p9096 = .success := by decide +kernel
theorem unsat9096 : Unsatisfiable (PosFin 65) f9096 := by
  apply lratCheckerSound f9096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9096
  · intro a ha; simp [p9096] at ha; subst a; trivial
  · exact checked9096
theorem derived9096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9096 := by
  apply localUnsat_implies_entails f9096 [c5258, c5156] c9096 unsat9096 (by rfl) a
  have h0 : Entails.eval a c5258 := h 5257 (by decide)
  have h1 : Entails.eval a c5156 := h 5155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9097 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9079, some c9064, some c7129, some c9080, some c9081, some c4979, some c9083, some c9095, some c5530, some c5281, some c9096, some c5300, some c5863, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9097 : lratChecker f9097 p9097 = .success := by decide +kernel
theorem unsat9097 : Unsatisfiable (PosFin 65) f9097 := by
  apply lratCheckerSound f9097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9097
  · intro a ha; simp [p9097] at ha; subst a; trivial
  · exact checked9097
theorem derived9097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9097 := by
  apply localUnsat_implies_entails f9097 [c9079, c9064, c7129, c9080, c9081, c4979, c9083, c9095, c5530, c5281, c9096, c5300, c5863] c9097 unsat9097 (by rfl) a
  have h0 : Entails.eval a c9079 := derived9079 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9080 := derived9080 a h
  have h4 : Entails.eval a c9081 := derived9081 a h
  have h5 : Entails.eval a c4979 := h 4978 (by decide)
  have h6 : Entails.eval a c9083 := derived9083 a h
  have h7 : Entails.eval a c9095 := derived9095 a h
  have h8 : Entails.eval a c5530 := h 5529 (by decide)
  have h9 : Entails.eval a c5281 := h 5280 (by decide)
  have h10 : Entails.eval a c9096 := derived9096 a h
  have h11 : Entails.eval a c5300 := h 5299 (by decide)
  have h12 : Entails.eval a c5863 := h 5862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9098 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c9066, some c5863, some c5708, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9098 : lratChecker f9098 p9098 = .success := by decide +kernel
theorem unsat9098 : Unsatisfiable (PosFin 65) f9098 := by
  apply lratCheckerSound f9098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9098
  · intro a ha; simp [p9098] at ha; subst a; trivial
  · exact checked9098
theorem derived9098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9098 := by
  apply localUnsat_implies_entails f9098 [c9064, c9066, c5863, c5708] c9098 unsat9098 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c9066 := derived9066 a h
  have h2 : Entails.eval a c5863 := h 5862 (by decide)
  have h3 : Entails.eval a c5708 := h 5707 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9099 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5711, some c5713, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9099 : lratChecker f9099 p9099 = .success := by decide +kernel
theorem unsat9099 : Unsatisfiable (PosFin 65) f9099 := by
  apply lratCheckerSound f9099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9099
  · intro a ha; simp [p9099] at ha; subst a; trivial
  · exact checked9099
theorem derived9099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9099 := by
  apply localUnsat_implies_entails f9099 [c5711, c5713] c9099 unsat9099 (by rfl) a
  have h0 : Entails.eval a c5711 := h 5710 (by decide)
  have h1 : Entails.eval a c5713 := h 5712 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9100 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3455, some c3426, some c4837, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9100 : lratChecker f9100 p9100 = .success := by decide +kernel
theorem unsat9100 : Unsatisfiable (PosFin 65) f9100 := by
  apply lratCheckerSound f9100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9100
  · intro a ha; simp [p9100] at ha; subst a; trivial
  · exact checked9100
theorem derived9100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9100 := by
  apply localUnsat_implies_entails f9100 [c3455, c3426, c4837] c9100 unsat9100 (by rfl) a
  have h0 : Entails.eval a c3455 := h 3454 (by decide)
  have h1 : Entails.eval a c3426 := h 3425 (by decide)
  have h2 : Entails.eval a c4837 := h 4836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9101 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9099, some c5403, some c5319, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9101 : lratChecker f9101 p9101 = .success := by decide +kernel
theorem unsat9101 : Unsatisfiable (PosFin 65) f9101 := by
  apply lratCheckerSound f9101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9101
  · intro a ha; simp [p9101] at ha; subst a; trivial
  · exact checked9101
theorem derived9101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9101 := by
  apply localUnsat_implies_entails f9101 [c9099, c5403, c5319] c9101 unsat9101 (by rfl) a
  have h0 : Entails.eval a c9099 := derived9099 a h
  have h1 : Entails.eval a c5403 := h 5402 (by decide)
  have h2 : Entails.eval a c5319 := h 5318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9102 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9097, some c9079, some c9064, some c7129, some c9098, some c9100, some c9101, some c5866, some c9065, some c6986, some c5861, some c5534, some c5203, some c4145, some c4404, some c5161, some c3553, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9102 : lratChecker f9102 p9102 = .success := by decide +kernel
theorem unsat9102 : Unsatisfiable (PosFin 65) f9102 := by
  apply lratCheckerSound f9102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9102
  · intro a ha; simp [p9102] at ha; subst a; trivial
  · exact checked9102
theorem derived9102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9102 := by
  apply localUnsat_implies_entails f9102 [c9097, c9079, c9064, c7129, c9098, c9100, c9101, c5866, c9065, c6986, c5861, c5534, c5203, c4145, c4404, c5161, c3553] c9102 unsat9102 (by rfl) a
  have h0 : Entails.eval a c9097 := derived9097 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9098 := derived9098 a h
  have h5 : Entails.eval a c9100 := derived9100 a h
  have h6 : Entails.eval a c9101 := derived9101 a h
  have h7 : Entails.eval a c5866 := h 5865 (by decide)
  have h8 : Entails.eval a c9065 := derived9065 a h
  have h9 : Entails.eval a c6986 := derived6986 a h
  have h10 : Entails.eval a c5861 := h 5860 (by decide)
  have h11 : Entails.eval a c5534 := h 5533 (by decide)
  have h12 : Entails.eval a c5203 := h 5202 (by decide)
  have h13 : Entails.eval a c4145 := h 4144 (by decide)
  have h14 : Entails.eval a c4404 := h 4403 (by decide)
  have h15 : Entails.eval a c5161 := h 5160 (by decide)
  have h16 : Entails.eval a c3553 := h 3552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9103 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5866, some c5864, some c6635, some c5874, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9103 : lratChecker f9103 p9103 = .success := by decide +kernel
theorem unsat9103 : Unsatisfiable (PosFin 65) f9103 := by
  apply lratCheckerSound f9103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9103
  · intro a ha; simp [p9103] at ha; subst a; trivial
  · exact checked9103
theorem derived9103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9103 := by
  apply localUnsat_implies_entails f9103 [c5866, c5864, c6635, c5874] c9103 unsat9103 (by rfl) a
  have h0 : Entails.eval a c5866 := h 5865 (by decide)
  have h1 : Entails.eval a c5864 := h 5863 (by decide)
  have h2 : Entails.eval a c6635 := derived6635 a h
  have h3 : Entails.eval a c5874 := h 5873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9104 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨63, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨60, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9065, some c9103, some c5319, some c9074, some c4497, some c4429, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9104 : lratChecker f9104 p9104 = .success := by decide +kernel
theorem unsat9104 : Unsatisfiable (PosFin 65) f9104 := by
  apply lratCheckerSound f9104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9104
  · intro a ha; simp [p9104] at ha; subst a; trivial
  · exact checked9104
theorem derived9104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9104 := by
  apply localUnsat_implies_entails f9104 [c9065, c9103, c5319, c9074, c4497, c4429] c9104 unsat9104 (by rfl) a
  have h0 : Entails.eval a c9065 := derived9065 a h
  have h1 : Entails.eval a c9103 := derived9103 a h
  have h2 : Entails.eval a c5319 := h 5318 (by decide)
  have h3 : Entails.eval a c9074 := derived9074 a h
  have h4 : Entails.eval a c4497 := h 4496 (by decide)
  have h5 : Entails.eval a c4429 := h 4428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9105 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨63, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9074, some c9069, some c6631, some c3437, some c6867, some c6871, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9105 : lratChecker f9105 p9105 = .success := by decide +kernel
theorem unsat9105 : Unsatisfiable (PosFin 65) f9105 := by
  apply lratCheckerSound f9105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9105
  · intro a ha; simp [p9105] at ha; subst a; trivial
  · exact checked9105
theorem derived9105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9105 := by
  apply localUnsat_implies_entails f9105 [c7129, c9074, c9069, c6631, c3437, c6867, c6871] c9105 unsat9105 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9074 := derived9074 a h
  have h2 : Entails.eval a c9069 := derived9069 a h
  have h3 : Entails.eval a c6631 := derived6631 a h
  have h4 : Entails.eval a c3437 := h 3436 (by decide)
  have h5 : Entails.eval a c6867 := derived6867 a h
  have h6 : Entails.eval a c6871 := derived6871 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9106 : DefaultClause 65 := directClause [(⟨37, by decide⟩, true), (⟨46, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6631, some c6986, some c3437, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9106 : lratChecker f9106 p9106 = .success := by decide +kernel
theorem unsat9106 : Unsatisfiable (PosFin 65) f9106 := by
  apply lratCheckerSound f9106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9106
  · intro a ha; simp [p9106] at ha; subst a; trivial
  · exact checked9106
theorem derived9106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9106 := by
  apply localUnsat_implies_entails f9106 [c6631, c6986, c3437] c9106 unsat9106 (by rfl) a
  have h0 : Entails.eval a c6631 := derived6631 a h
  have h1 : Entails.eval a c6986 := derived6986 a h
  have h2 : Entails.eval a c3437 := h 3436 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9107 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9102, some c9097, some c9079, some c9064, some c7129, some c9104, some c9105, some c9106, some c9070, some c9069, some c5100, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9107 : lratChecker f9107 p9107 = .success := by decide +kernel
theorem unsat9107 : Unsatisfiable (PosFin 65) f9107 := by
  apply lratCheckerSound f9107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9107
  · intro a ha; simp [p9107] at ha; subst a; trivial
  · exact checked9107
theorem derived9107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9107 := by
  apply localUnsat_implies_entails f9107 [c9102, c9097, c9079, c9064, c7129, c9104, c9105, c9106, c9070, c9069, c5100] c9107 unsat9107 (by rfl) a
  have h0 : Entails.eval a c9102 := derived9102 a h
  have h1 : Entails.eval a c9097 := derived9097 a h
  have h2 : Entails.eval a c9079 := derived9079 a h
  have h3 : Entails.eval a c9064 := derived9064 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c9104 := derived9104 a h
  have h6 : Entails.eval a c9105 := derived9105 a h
  have h7 : Entails.eval a c9106 := derived9106 a h
  have h8 : Entails.eval a c9070 := derived9070 a h
  have h9 : Entails.eval a c9069 := derived9069 a h
  have h10 : Entails.eval a c5100 := h 5099 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9108 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c5859, some c5736, some c5705, some c4493, some c4109, some c4458, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9108 : lratChecker f9108 p9108 = .success := by decide +kernel
theorem unsat9108 : Unsatisfiable (PosFin 65) f9108 := by
  apply lratCheckerSound f9108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9108
  · intro a ha; simp [p9108] at ha; subst a; trivial
  · exact checked9108
theorem derived9108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9108 := by
  apply localUnsat_implies_entails f9108 [c9064, c5859, c5736, c5705, c4493, c4109, c4458] c9108 unsat9108 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c5859 := h 5858 (by decide)
  have h2 : Entails.eval a c5736 := h 5735 (by decide)
  have h3 : Entails.eval a c5705 := h 5704 (by decide)
  have h4 : Entails.eval a c4493 := h 4492 (by decide)
  have h5 : Entails.eval a c4109 := h 4108 (by decide)
  have h6 : Entails.eval a c4458 := h 4457 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9109 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6869, some c6870, some c3437, some c4682, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9109 : lratChecker f9109 p9109 = .success := by decide +kernel
theorem unsat9109 : Unsatisfiable (PosFin 65) f9109 := by
  apply lratCheckerSound f9109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9109
  · intro a ha; simp [p9109] at ha; subst a; trivial
  · exact checked9109
theorem derived9109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9109 := by
  apply localUnsat_implies_entails f9109 [c6869, c6870, c3437, c4682] c9109 unsat9109 (by rfl) a
  have h0 : Entails.eval a c6869 := derived6869 a h
  have h1 : Entails.eval a c6870 := derived6870 a h
  have h2 : Entails.eval a c3437 := h 3436 (by decide)
  have h3 : Entails.eval a c4682 := h 4681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9110 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9097, some c9079, some c9064, some c7129, some c9108, some c9107, some c9067, some c9109, some c3562, some c6788, some c4487, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9110 : lratChecker f9110 p9110 = .success := by decide +kernel
theorem unsat9110 : Unsatisfiable (PosFin 65) f9110 := by
  apply lratCheckerSound f9110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9110
  · intro a ha; simp [p9110] at ha; subst a; trivial
  · exact checked9110
theorem derived9110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9110 := by
  apply localUnsat_implies_entails f9110 [c9097, c9079, c9064, c7129, c9108, c9107, c9067, c9109, c3562, c6788, c4487] c9110 unsat9110 (by rfl) a
  have h0 : Entails.eval a c9097 := derived9097 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9108 := derived9108 a h
  have h5 : Entails.eval a c9107 := derived9107 a h
  have h6 : Entails.eval a c9067 := derived9067 a h
  have h7 : Entails.eval a c9109 := derived9109 a h
  have h8 : Entails.eval a c3562 := h 3561 (by decide)
  have h9 : Entails.eval a c6788 := derived6788 a h
  have h10 : Entails.eval a c4487 := h 4486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9111 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c5668, some c7024, some c3496, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9111 : lratChecker f9111 p9111 = .success := by decide +kernel
theorem unsat9111 : Unsatisfiable (PosFin 65) f9111 := by
  apply lratCheckerSound f9111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9111
  · intro a ha; simp [p9111] at ha; subst a; trivial
  · exact checked9111
theorem derived9111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9111 := by
  apply localUnsat_implies_entails f9111 [c7129, c5668, c7024, c3496] c9111 unsat9111 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c5668 := h 5667 (by decide)
  have h2 : Entails.eval a c7024 := derived7024 a h
  have h3 : Entails.eval a c3496 := h 3495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9112 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c9079, some c9097, some c9110, some c9111, some c7129, some c3437, some c3494, some c4768, some c3496, some c4849, some c6922, some c5276, some c6193, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9112 : lratChecker f9112 p9112 = .success := by decide +kernel
theorem unsat9112 : Unsatisfiable (PosFin 65) f9112 := by
  apply lratCheckerSound f9112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9112
  · intro a ha; simp [p9112] at ha; subst a; trivial
  · exact checked9112
theorem derived9112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9112 := by
  apply localUnsat_implies_entails f9112 [c9064, c9079, c9097, c9110, c9111, c7129, c3437, c3494, c4768, c3496, c4849, c6922, c5276, c6193] c9112 unsat9112 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9097 := derived9097 a h
  have h3 : Entails.eval a c9110 := derived9110 a h
  have h4 : Entails.eval a c9111 := derived9111 a h
  have h5 : Entails.eval a c7129 := derived7129 a h
  have h6 : Entails.eval a c3437 := h 3436 (by decide)
  have h7 : Entails.eval a c3494 := h 3493 (by decide)
  have h8 : Entails.eval a c4768 := h 4767 (by decide)
  have h9 : Entails.eval a c3496 := h 3495 (by decide)
  have h10 : Entails.eval a c4849 := h 4848 (by decide)
  have h11 : Entails.eval a c6922 := derived6922 a h
  have h12 : Entails.eval a c5276 := h 5275 (by decide)
  have h13 : Entails.eval a c6193 := derived6193 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9113 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c9079, some c9097, some c9110, some c9111, some c9112, some c7027, some c6863, some c7034, some c6903, some c6812, some c3533, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9113 : lratChecker f9113 p9113 = .success := by decide +kernel
theorem unsat9113 : Unsatisfiable (PosFin 65) f9113 := by
  apply lratCheckerSound f9113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9113
  · intro a ha; simp [p9113] at ha; subst a; trivial
  · exact checked9113
theorem derived9113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9113 := by
  apply localUnsat_implies_entails f9113 [c9064, c9079, c9097, c9110, c9111, c9112, c7027, c6863, c7034, c6903, c6812, c3533] c9113 unsat9113 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9097 := derived9097 a h
  have h3 : Entails.eval a c9110 := derived9110 a h
  have h4 : Entails.eval a c9111 := derived9111 a h
  have h5 : Entails.eval a c9112 := derived9112 a h
  have h6 : Entails.eval a c7027 := derived7027 a h
  have h7 : Entails.eval a c6863 := derived6863 a h
  have h8 : Entails.eval a c7034 := derived7034 a h
  have h9 : Entails.eval a c6903 := derived6903 a h
  have h10 : Entails.eval a c6812 := derived6812 a h
  have h11 : Entails.eval a c3533 := h 3532 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9114 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c9079, some c9097, some c9110, some c9111, some c9113, some c5299, some c5689, some c5394, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9114 : lratChecker f9114 p9114 = .success := by decide +kernel
theorem unsat9114 : Unsatisfiable (PosFin 65) f9114 := by
  apply lratCheckerSound f9114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9114
  · intro a ha; simp [p9114] at ha; subst a; trivial
  · exact checked9114
theorem derived9114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9114 := by
  apply localUnsat_implies_entails f9114 [c9064, c9079, c9097, c9110, c9111, c9113, c5299, c5689, c5394] c9114 unsat9114 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9097 := derived9097 a h
  have h3 : Entails.eval a c9110 := derived9110 a h
  have h4 : Entails.eval a c9111 := derived9111 a h
  have h5 : Entails.eval a c9113 := derived9113 a h
  have h6 : Entails.eval a c5299 := h 5298 (by decide)
  have h7 : Entails.eval a c5689 := h 5688 (by decide)
  have h8 : Entails.eval a c5394 := h 5393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9115 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5299, some c5689, some c5394, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9115 : lratChecker f9115 p9115 = .success := by decide +kernel
theorem unsat9115 : Unsatisfiable (PosFin 65) f9115 := by
  apply lratCheckerSound f9115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9115
  · intro a ha; simp [p9115] at ha; subst a; trivial
  · exact checked9115
theorem derived9115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9115 := by
  apply localUnsat_implies_entails f9115 [c5299, c5689, c5394] c9115 unsat9115 (by rfl) a
  have h0 : Entails.eval a c5299 := h 5298 (by decide)
  have h1 : Entails.eval a c5689 := h 5688 (by decide)
  have h2 : Entails.eval a c5394 := h 5393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9116 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨45, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5406, some c7005, some c7001, some c5407, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9116 : lratChecker f9116 p9116 = .success := by decide +kernel
theorem unsat9116 : Unsatisfiable (PosFin 65) f9116 := by
  apply lratCheckerSound f9116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9116
  · intro a ha; simp [p9116] at ha; subst a; trivial
  · exact checked9116
theorem derived9116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9116 := by
  apply localUnsat_implies_entails f9116 [c5406, c7005, c7001, c5407] c9116 unsat9116 (by rfl) a
  have h0 : Entails.eval a c5406 := h 5405 (by decide)
  have h1 : Entails.eval a c7005 := derived7005 a h
  have h2 : Entails.eval a c7001 := derived7001 a h
  have h3 : Entails.eval a c5407 := h 5406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9117 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨34, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c7129, some c9116, some c5298, some c3482, some c5306, some c5511, some c5781, some c5270, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9117 : lratChecker f9117 p9117 = .success := by decide +kernel
theorem unsat9117 : Unsatisfiable (PosFin 65) f9117 := by
  apply lratCheckerSound f9117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9117
  · intro a ha; simp [p9117] at ha; subst a; trivial
  · exact checked9117
theorem derived9117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9117 := by
  apply localUnsat_implies_entails f9117 [c9115, c7129, c9116, c5298, c3482, c5306, c5511, c5781, c5270] c9117 unsat9117 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9116 := derived9116 a h
  have h3 : Entails.eval a c5298 := h 5297 (by decide)
  have h4 : Entails.eval a c3482 := h 3481 (by decide)
  have h5 : Entails.eval a c5306 := h 5305 (by decide)
  have h6 : Entails.eval a c5511 := h 5510 (by decide)
  have h7 : Entails.eval a c5781 := h 5780 (by decide)
  have h8 : Entails.eval a c5270 := h 5269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9118 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9117, some c6861, some c6859, some c4292, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9118 : lratChecker f9118 p9118 = .success := by decide +kernel
theorem unsat9118 : Unsatisfiable (PosFin 65) f9118 := by
  apply lratCheckerSound f9118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9118
  · intro a ha; simp [p9118] at ha; subst a; trivial
  · exact checked9118
theorem derived9118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9118 := by
  apply localUnsat_implies_entails f9118 [c7129, c9117, c6861, c6859, c4292] c9118 unsat9118 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9117 := derived9117 a h
  have h2 : Entails.eval a c6861 := derived6861 a h
  have h3 : Entails.eval a c6859 := derived6859 a h
  have h4 : Entails.eval a c4292 := h 4291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9119 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨49, by decide⟩, true), (⟨44, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c7027, some c5688, some c5702, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9119 : lratChecker f9119 p9119 = .success := by decide +kernel
theorem unsat9119 : Unsatisfiable (PosFin 65) f9119 := by
  apply lratCheckerSound f9119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9119
  · intro a ha; simp [p9119] at ha; subst a; trivial
  · exact checked9119
theorem derived9119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9119 := by
  apply localUnsat_implies_entails f9119 [c7129, c7027, c5688, c5702] c9119 unsat9119 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c7027 := derived7027 a h
  have h2 : Entails.eval a c5688 := h 5687 (by decide)
  have h3 : Entails.eval a c5702 := h 5701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9120 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c9118, some c9119, some c9116, some c5298, some c5306, some c4237, some c5516, some c5270, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9120 : lratChecker f9120 p9120 = .success := by decide +kernel
theorem unsat9120 : Unsatisfiable (PosFin 65) f9120 := by
  apply lratCheckerSound f9120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9120
  · intro a ha; simp [p9120] at ha; subst a; trivial
  · exact checked9120
theorem derived9120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9120 := by
  apply localUnsat_implies_entails f9120 [c9115, c9118, c9119, c9116, c5298, c5306, c4237, c5516, c5270] c9120 unsat9120 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c9118 := derived9118 a h
  have h2 : Entails.eval a c9119 := derived9119 a h
  have h3 : Entails.eval a c9116 := derived9116 a h
  have h4 : Entails.eval a c5298 := h 5297 (by decide)
  have h5 : Entails.eval a c5306 := h 5305 (by decide)
  have h6 : Entails.eval a c4237 := h 4236 (by decide)
  have h7 : Entails.eval a c5516 := h 5515 (by decide)
  have h8 : Entails.eval a c5270 := h 5269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9121 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨45, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true), (⟨60, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c7129, some c9072, some c4322, some c5406, some c5320, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9121 : lratChecker f9121 p9121 = .success := by decide +kernel
theorem unsat9121 : Unsatisfiable (PosFin 65) f9121 := by
  apply lratCheckerSound f9121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9121
  · intro a ha; simp [p9121] at ha; subst a; trivial
  · exact checked9121
theorem derived9121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9121 := by
  apply localUnsat_implies_entails f9121 [c9064, c7129, c9072, c4322, c5406, c5320] c9121 unsat9121 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9072 := derived9072 a h
  have h3 : Entails.eval a c4322 := h 4321 (by decide)
  have h4 : Entails.eval a c5406 := h 5405 (by decide)
  have h5 : Entails.eval a c5320 := h 5319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9122 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨62, by decide⟩, false), (⟨44, by decide⟩, false), (⟨58, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3496, some c3502, some c6778, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p9122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9122 : lratChecker f9122 p9122 = .success := by decide +kernel
theorem unsat9122 : Unsatisfiable (PosFin 65) f9122 := by
  apply lratCheckerSound f9122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9122
  · intro a ha; simp [p9122] at ha; subst a; trivial
  · exact checked9122
theorem derived9122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9122 := by
  apply localUnsat_implies_entails f9122 [c3496, c3502, c6778] c9122 unsat9122 (by rfl) a
  have h0 : Entails.eval a c3496 := h 3495 (by decide)
  have h1 : Entails.eval a c3502 := h 3501 (by decide)
  have h2 : Entails.eval a c6778 := derived6778 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9123 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c9114, some c9120, some c7129, some c9121, some c9122, some c3468, some c7039, some c5417, some c7017, some c6998, some c6897, some c6787, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9123 : lratChecker f9123 p9123 = .success := by decide +kernel
theorem unsat9123 : Unsatisfiable (PosFin 65) f9123 := by
  apply lratCheckerSound f9123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9123
  · intro a ha; simp [p9123] at ha; subst a; trivial
  · exact checked9123
theorem derived9123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9123 := by
  apply localUnsat_implies_entails f9123 [c9064, c9114, c9120, c7129, c9121, c9122, c3468, c7039, c5417, c7017, c6998, c6897, c6787] c9123 unsat9123 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c9114 := derived9114 a h
  have h2 : Entails.eval a c9120 := derived9120 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9121 := derived9121 a h
  have h5 : Entails.eval a c9122 := derived9122 a h
  have h6 : Entails.eval a c3468 := h 3467 (by decide)
  have h7 : Entails.eval a c7039 := derived7039 a h
  have h8 : Entails.eval a c5417 := h 5416 (by decide)
  have h9 : Entails.eval a c7017 := derived7017 a h
  have h10 : Entails.eval a c6998 := derived6998 a h
  have h11 : Entails.eval a c6897 := derived6897 a h
  have h12 : Entails.eval a c6787 := derived6787 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9124 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9114, some c9064, some c7129, some c9120, some c9123, some c5687, some c5691, some c7029, some c6970, some c5692, some c5537, some c4325, some c5685, some c4115, some c6846, some c5168, some c5349, some c5270, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9124 : lratChecker f9124 p9124 = .success := by decide +kernel
theorem unsat9124 : Unsatisfiable (PosFin 65) f9124 := by
  apply lratCheckerSound f9124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9124
  · intro a ha; simp [p9124] at ha; subst a; trivial
  · exact checked9124
theorem derived9124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9124 := by
  apply localUnsat_implies_entails f9124 [c9114, c9064, c7129, c9120, c9123, c5687, c5691, c7029, c6970, c5692, c5537, c4325, c5685, c4115, c6846, c5168, c5349, c5270] c9124 unsat9124 (by rfl) a
  have h0 : Entails.eval a c9114 := derived9114 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9120 := derived9120 a h
  have h4 : Entails.eval a c9123 := derived9123 a h
  have h5 : Entails.eval a c5687 := h 5686 (by decide)
  have h6 : Entails.eval a c5691 := h 5690 (by decide)
  have h7 : Entails.eval a c7029 := derived7029 a h
  have h8 : Entails.eval a c6970 := derived6970 a h
  have h9 : Entails.eval a c5692 := h 5691 (by decide)
  have h10 : Entails.eval a c5537 := h 5536 (by decide)
  have h11 : Entails.eval a c4325 := h 4324 (by decide)
  have h12 : Entails.eval a c5685 := h 5684 (by decide)
  have h13 : Entails.eval a c4115 := h 4114 (by decide)
  have h14 : Entails.eval a c6846 := derived6846 a h
  have h15 : Entails.eval a c5168 := h 5167 (by decide)
  have h16 : Entails.eval a c5349 := h 5348 (by decide)
  have h17 : Entails.eval a c5270 := h 5269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9125 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨45, by decide⟩, false), (⟨59, by decide⟩, false), (⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2706, some c3092, some c3081, some c3270, some c3360, some c3212, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9125 : lratChecker f9125 p9125 = .success := by decide +kernel
theorem unsat9125 : Unsatisfiable (PosFin 65) f9125 := by
  apply lratCheckerSound f9125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9125
  · intro a ha; simp [p9125] at ha; subst a; trivial
  · exact checked9125
theorem derived9125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9125 := by
  apply localUnsat_implies_entails f9125 [c2706, c3092, c3081, c3270, c3360, c3212] c9125 unsat9125 (by rfl) a
  have h0 : Entails.eval a c2706 := h 2705 (by decide)
  have h1 : Entails.eval a c3092 := h 3091 (by decide)
  have h2 : Entails.eval a c3081 := h 3080 (by decide)
  have h3 : Entails.eval a c3270 := h 3269 (by decide)
  have h4 : Entails.eval a c3360 := h 3359 (by decide)
  have h5 : Entails.eval a c3212 := h 3211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9126 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨62, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2959, some c6769, some c2694, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9126 : lratChecker f9126 p9126 = .success := by decide +kernel
theorem unsat9126 : Unsatisfiable (PosFin 65) f9126 := by
  apply lratCheckerSound f9126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9126
  · intro a ha; simp [p9126] at ha; subst a; trivial
  · exact checked9126
theorem derived9126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9126 := by
  apply localUnsat_implies_entails f9126 [c2959, c6769, c2694] c9126 unsat9126 (by rfl) a
  have h0 : Entails.eval a c2959 := h 2958 (by decide)
  have h1 : Entails.eval a c6769 := derived6769 a h
  have h2 : Entails.eval a c2694 := h 2693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9127 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨24, by decide⟩, true), (⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨63, by decide⟩, false), (⟨49, by decide⟩, false), (⟨44, by decide⟩, false), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2843, some c2889, some c6732, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p9127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9127 : lratChecker f9127 p9127 = .success := by decide +kernel
theorem unsat9127 : Unsatisfiable (PosFin 65) f9127 := by
  apply lratCheckerSound f9127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9127
  · intro a ha; simp [p9127] at ha; subst a; trivial
  · exact checked9127
theorem derived9127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9127 := by
  apply localUnsat_implies_entails f9127 [c2843, c2889, c6732] c9127 unsat9127 (by rfl) a
  have h0 : Entails.eval a c2843 := h 2842 (by decide)
  have h1 : Entails.eval a c2889 := h 2888 (by decide)
  have h2 : Entails.eval a c6732 := derived6732 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9128 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨59, by decide⟩, false), (⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true), (⟨57, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3868, some c9125, some c9126, some c9127, some c3344, some c3409, some c3316, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9128 : lratChecker f9128 p9128 = .success := by decide +kernel
theorem unsat9128 : Unsatisfiable (PosFin 65) f9128 := by
  apply lratCheckerSound f9128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9128
  · intro a ha; simp [p9128] at ha; subst a; trivial
  · exact checked9128
theorem derived9128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9128 := by
  apply localUnsat_implies_entails f9128 [c3868, c9125, c9126, c9127, c3344, c3409, c3316] c9128 unsat9128 (by rfl) a
  have h0 : Entails.eval a c3868 := h 3867 (by decide)
  have h1 : Entails.eval a c9125 := derived9125 a h
  have h2 : Entails.eval a c9126 := derived9126 a h
  have h3 : Entails.eval a c9127 := derived9127 a h
  have h4 : Entails.eval a c3344 := h 3343 (by decide)
  have h5 : Entails.eval a c3409 := h 3408 (by decide)
  have h6 : Entails.eval a c3316 := h 3315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9129 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9124, some c9114, some c9064, some c7129, some c5667, some c5670, some c3863, some c5062, some c3830, some c3868, some c7026, some c6814, some c6790, some c5673, some c5674, some c5349, some c5683, some c4406, some c6819, some c3445, some c4305, some c5289, some c6913, some c4464, some c9128, some c2783, some c9086, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked9129 : lratChecker f9129 p9129 = .success := by decide +kernel
theorem unsat9129 : Unsatisfiable (PosFin 65) f9129 := by
  apply lratCheckerSound f9129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9129
  · intro a ha; simp [p9129] at ha; subst a; trivial
  · exact checked9129
theorem derived9129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9129 := by
  apply localUnsat_implies_entails f9129 [c9124, c9114, c9064, c7129, c5667, c5670, c3863, c5062, c3830, c3868, c7026, c6814, c6790, c5673, c5674, c5349, c5683, c4406, c6819, c3445, c4305, c5289, c6913, c4464, c9128, c2783, c9086] c9129 unsat9129 (by rfl) a
  have h0 : Entails.eval a c9124 := derived9124 a h
  have h1 : Entails.eval a c9114 := derived9114 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c5667 := h 5666 (by decide)
  have h5 : Entails.eval a c5670 := h 5669 (by decide)
  have h6 : Entails.eval a c3863 := h 3862 (by decide)
  have h7 : Entails.eval a c5062 := h 5061 (by decide)
  have h8 : Entails.eval a c3830 := h 3829 (by decide)
  have h9 : Entails.eval a c3868 := h 3867 (by decide)
  have h10 : Entails.eval a c7026 := derived7026 a h
  have h11 : Entails.eval a c6814 := derived6814 a h
  have h12 : Entails.eval a c6790 := derived6790 a h
  have h13 : Entails.eval a c5673 := h 5672 (by decide)
  have h14 : Entails.eval a c5674 := h 5673 (by decide)
  have h15 : Entails.eval a c5349 := h 5348 (by decide)
  have h16 : Entails.eval a c5683 := h 5682 (by decide)
  have h17 : Entails.eval a c4406 := h 4405 (by decide)
  have h18 : Entails.eval a c6819 := derived6819 a h
  have h19 : Entails.eval a c3445 := h 3444 (by decide)
  have h20 : Entails.eval a c4305 := h 4304 (by decide)
  have h21 : Entails.eval a c5289 := h 5288 (by decide)
  have h22 : Entails.eval a c6913 := derived6913 a h
  have h23 : Entails.eval a c4464 := h 4463 (by decide)
  have h24 : Entails.eval a c9128 := derived9128 a h
  have h25 : Entails.eval a c2783 := h 2782 (by decide)
  have h26 : Entails.eval a c9086 := derived9086 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9130 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c7129, some c9124, some c9129, some c5668, some c7024, some c3882, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9130 : lratChecker f9130 p9130 = .success := by decide +kernel
theorem unsat9130 : Unsatisfiable (PosFin 65) f9130 := by
  apply lratCheckerSound f9130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9130
  · intro a ha; simp [p9130] at ha; subst a; trivial
  · exact checked9130
theorem derived9130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9130 := by
  apply localUnsat_implies_entails f9130 [c9064, c7129, c9124, c9129, c5668, c7024, c3882] c9130 unsat9130 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9124 := derived9124 a h
  have h3 : Entails.eval a c9129 := derived9129 a h
  have h4 : Entails.eval a c5668 := h 5667 (by decide)
  have h5 : Entails.eval a c7024 := derived7024 a h
  have h6 : Entails.eval a c3882 := h 3881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9131 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨62, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3846, some c5749, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9131 : lratChecker f9131 p9131 = .success := by decide +kernel
theorem unsat9131 : Unsatisfiable (PosFin 65) f9131 := by
  apply lratCheckerSound f9131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9131
  · intro a ha; simp [p9131] at ha; subst a; trivial
  · exact checked9131
theorem derived9131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9131 := by
  apply localUnsat_implies_entails f9131 [c3846, c5749] c9131 unsat9131 (by rfl) a
  have h0 : Entails.eval a c3846 := h 3845 (by decide)
  have h1 : Entails.eval a c5749 := h 5748 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9132 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨44, by decide⟩, true), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6962, some c6887, some c6869, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p9132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9132 : lratChecker f9132 p9132 = .success := by decide +kernel
theorem unsat9132 : Unsatisfiable (PosFin 65) f9132 := by
  apply lratCheckerSound f9132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9132
  · intro a ha; simp [p9132] at ha; subst a; trivial
  · exact checked9132
theorem derived9132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9132 := by
  apply localUnsat_implies_entails f9132 [c6962, c6887, c6869] c9132 unsat9132 (by rfl) a
  have h0 : Entails.eval a c6962 := derived6962 a h
  have h1 : Entails.eval a c6887 := derived6887 a h
  have h2 : Entails.eval a c6869 := derived6869 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9133 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨44, by decide⟩, true), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9132, some c9131, some c6966, some c6889, some c6870, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9133 : lratChecker f9133 p9133 = .success := by decide +kernel
theorem unsat9133 : Unsatisfiable (PosFin 65) f9133 := by
  apply lratCheckerSound f9133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9133
  · intro a ha; simp [p9133] at ha; subst a; trivial
  · exact checked9133
theorem derived9133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9133 := by
  apply localUnsat_implies_entails f9133 [c9132, c9131, c6966, c6889, c6870] c9133 unsat9133 (by rfl) a
  have h0 : Entails.eval a c9132 := derived9132 a h
  have h1 : Entails.eval a c9131 := derived9131 a h
  have h2 : Entails.eval a c6966 := derived6966 a h
  have h3 : Entails.eval a c6889 := derived6889 a h
  have h4 : Entails.eval a c6870 := derived6870 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9134 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨49, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9064, some c9114, some c9130, some c9133, some c5735, some c3468, some c6810, some c4230, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9134 : lratChecker f9134 p9134 = .success := by decide +kernel
theorem unsat9134 : Unsatisfiable (PosFin 65) f9134 := by
  apply lratCheckerSound f9134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9134
  · intro a ha; simp [p9134] at ha; subst a; trivial
  · exact checked9134
theorem derived9134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9134 := by
  apply localUnsat_implies_entails f9134 [c7129, c9064, c9114, c9130, c9133, c5735, c3468, c6810, c4230] c9134 unsat9134 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c9114 := derived9114 a h
  have h3 : Entails.eval a c9130 := derived9130 a h
  have h4 : Entails.eval a c9133 := derived9133 a h
  have h5 : Entails.eval a c5735 := h 5734 (by decide)
  have h6 : Entails.eval a c3468 := h 3467 (by decide)
  have h7 : Entails.eval a c6810 := derived6810 a h
  have h8 : Entails.eval a c4230 := h 4229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9135 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨63, by decide⟩, false), (⟨34, by decide⟩, true), (⟨62, by decide⟩, false), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4248, some c6853, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9135 : lratChecker f9135 p9135 = .success := by decide +kernel
theorem unsat9135 : Unsatisfiable (PosFin 65) f9135 := by
  apply lratCheckerSound f9135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9135
  · intro a ha; simp [p9135] at ha; subst a; trivial
  · exact checked9135
theorem derived9135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9135 := by
  apply localUnsat_implies_entails f9135 [c4248, c6853] c9135 unsat9135 (by rfl) a
  have h0 : Entails.eval a c4248 := h 4247 (by decide)
  have h1 : Entails.eval a c6853 := derived6853 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9136 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9134, some c7129, some c9064, some c9114, some c9130, some c9133, some c9073, some c9135, some c3811, some c3809, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9136 : lratChecker f9136 p9136 = .success := by decide +kernel
theorem unsat9136 : Unsatisfiable (PosFin 65) f9136 := by
  apply lratCheckerSound f9136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9136
  · intro a ha; simp [p9136] at ha; subst a; trivial
  · exact checked9136
theorem derived9136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9136 := by
  apply localUnsat_implies_entails f9136 [c9134, c7129, c9064, c9114, c9130, c9133, c9073, c9135, c3811, c3809] c9136 unsat9136 (by rfl) a
  have h0 : Entails.eval a c9134 := derived9134 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c9114 := derived9114 a h
  have h4 : Entails.eval a c9130 := derived9130 a h
  have h5 : Entails.eval a c9133 := derived9133 a h
  have h6 : Entails.eval a c9073 := derived9073 a h
  have h7 : Entails.eval a c9135 := derived9135 a h
  have h8 : Entails.eval a c3811 := h 3810 (by decide)
  have h9 : Entails.eval a c3809 := h 3808 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9137 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9134, some c9114, some c7129, some c9136, some c3454, some c3456, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9137 : lratChecker f9137 p9137 = .success := by decide +kernel
theorem unsat9137 : Unsatisfiable (PosFin 65) f9137 := by
  apply lratCheckerSound f9137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9137
  · intro a ha; simp [p9137] at ha; subst a; trivial
  · exact checked9137
theorem derived9137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9137 := by
  apply localUnsat_implies_entails f9137 [c9134, c9114, c7129, c9136, c3454, c3456] c9137 unsat9137 (by rfl) a
  have h0 : Entails.eval a c9134 := derived9134 a h
  have h1 : Entails.eval a c9114 := derived9114 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9136 := derived9136 a h
  have h4 : Entails.eval a c3454 := h 3453 (by decide)
  have h5 : Entails.eval a c3456 := h 3455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9138 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9130, some c9114, some c9064, some c7129, some c9133, some c9134, some c9137, some c5736, some c5745, some c5348, some c5749, some c5746, some c5743, some c9098, some c5320, some c5867, some c5872, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9138 : lratChecker f9138 p9138 = .success := by decide +kernel
theorem unsat9138 : Unsatisfiable (PosFin 65) f9138 := by
  apply lratCheckerSound f9138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9138
  · intro a ha; simp [p9138] at ha; subst a; trivial
  · exact checked9138
theorem derived9138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9138 := by
  apply localUnsat_implies_entails f9138 [c9130, c9114, c9064, c7129, c9133, c9134, c9137, c5736, c5745, c5348, c5749, c5746, c5743, c9098, c5320, c5867, c5872] c9138 unsat9138 (by rfl) a
  have h0 : Entails.eval a c9130 := derived9130 a h
  have h1 : Entails.eval a c9114 := derived9114 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9133 := derived9133 a h
  have h5 : Entails.eval a c9134 := derived9134 a h
  have h6 : Entails.eval a c9137 := derived9137 a h
  have h7 : Entails.eval a c5736 := h 5735 (by decide)
  have h8 : Entails.eval a c5745 := h 5744 (by decide)
  have h9 : Entails.eval a c5348 := h 5347 (by decide)
  have h10 : Entails.eval a c5749 := h 5748 (by decide)
  have h11 : Entails.eval a c5746 := h 5745 (by decide)
  have h12 : Entails.eval a c5743 := h 5742 (by decide)
  have h13 : Entails.eval a c9098 := derived9098 a h
  have h14 : Entails.eval a c5320 := h 5319 (by decide)
  have h15 : Entails.eval a c5867 := h 5866 (by decide)
  have h16 : Entails.eval a c5872 := h 5871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9139 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨62, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9138, some c9130, some c9114, some c9064, some c7129, some c5734, some c5742, some c5348, some c5749, some c5746, some c5743, some c5738, some c5320, some c5867, some c5872, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9139 : lratChecker f9139 p9139 = .success := by decide +kernel
theorem unsat9139 : Unsatisfiable (PosFin 65) f9139 := by
  apply lratCheckerSound f9139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9139
  · intro a ha; simp [p9139] at ha; subst a; trivial
  · exact checked9139
theorem derived9139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9139 := by
  apply localUnsat_implies_entails f9139 [c9138, c9130, c9114, c9064, c7129, c5734, c5742, c5348, c5749, c5746, c5743, c5738, c5320, c5867, c5872] c9139 unsat9139 (by rfl) a
  have h0 : Entails.eval a c9138 := derived9138 a h
  have h1 : Entails.eval a c9130 := derived9130 a h
  have h2 : Entails.eval a c9114 := derived9114 a h
  have h3 : Entails.eval a c9064 := derived9064 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c5734 := h 5733 (by decide)
  have h6 : Entails.eval a c5742 := h 5741 (by decide)
  have h7 : Entails.eval a c5348 := h 5347 (by decide)
  have h8 : Entails.eval a c5749 := h 5748 (by decide)
  have h9 : Entails.eval a c5746 := h 5745 (by decide)
  have h10 : Entails.eval a c5743 := h 5742 (by decide)
  have h11 : Entails.eval a c5738 := h 5737 (by decide)
  have h12 : Entails.eval a c5320 := h 5319 (by decide)
  have h13 : Entails.eval a c5867 := h 5866 (by decide)
  have h14 : Entails.eval a c5872 := h 5871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9140 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨60, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3830, some c3454, some c3806, some c4233, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p9140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9140 : lratChecker f9140 p9140 = .success := by decide +kernel
theorem unsat9140 : Unsatisfiable (PosFin 65) f9140 := by
  apply lratCheckerSound f9140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9140
  · intro a ha; simp [p9140] at ha; subst a; trivial
  · exact checked9140
theorem derived9140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9140 := by
  apply localUnsat_implies_entails f9140 [c3830, c3454, c3806, c4233] c9140 unsat9140 (by rfl) a
  have h0 : Entails.eval a c3830 := h 3829 (by decide)
  have h1 : Entails.eval a c3454 := h 3453 (by decide)
  have h2 : Entails.eval a c3806 := h 3805 (by decide)
  have h3 : Entails.eval a c4233 := h 4232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9141 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9138, some c9114, some c9064, some c7129, some c9139, some c9140, some c9072, some c3456, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9141 : lratChecker f9141 p9141 = .success := by decide +kernel
theorem unsat9141 : Unsatisfiable (PosFin 65) f9141 := by
  apply lratCheckerSound f9141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9141
  · intro a ha; simp [p9141] at ha; subst a; trivial
  · exact checked9141
theorem derived9141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9141 := by
  apply localUnsat_implies_entails f9141 [c9138, c9114, c9064, c7129, c9139, c9140, c9072, c3456] c9141 unsat9141 (by rfl) a
  have h0 : Entails.eval a c9138 := derived9138 a h
  have h1 : Entails.eval a c9114 := derived9114 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9139 := derived9139 a h
  have h5 : Entails.eval a c9140 := derived9140 a h
  have h6 : Entails.eval a c9072 := derived9072 a h
  have h7 : Entails.eval a c3456 := h 3455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9142 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9141, some c9138, some c9114, some c9064, some c7129, some c3468, some c9140, some c9072, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9142 : lratChecker f9142 p9142 = .success := by decide +kernel
theorem unsat9142 : Unsatisfiable (PosFin 65) f9142 := by
  apply lratCheckerSound f9142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9142
  · intro a ha; simp [p9142] at ha; subst a; trivial
  · exact checked9142
theorem derived9142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9142 := by
  apply localUnsat_implies_entails f9142 [c9141, c9138, c9114, c9064, c7129, c3468, c9140, c9072] c9142 unsat9142 (by rfl) a
  have h0 : Entails.eval a c9141 := derived9141 a h
  have h1 : Entails.eval a c9138 := derived9138 a h
  have h2 : Entails.eval a c9114 := derived9114 a h
  have h3 : Entails.eval a c9064 := derived9064 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c3468 := h 3467 (by decide)
  have h6 : Entails.eval a c9140 := derived9140 a h
  have h7 : Entails.eval a c9072 := derived9072 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9143 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨45, by decide⟩, false), (⟨35, by decide⟩, true), (⟨59, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true), (⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨44, by decide⟩, true), (⟨60, by decide⟩, true), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6956, some c2754, some c2783, some c2887, some c3346, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9143 : lratChecker f9143 p9143 = .success := by decide +kernel
theorem unsat9143 : Unsatisfiable (PosFin 65) f9143 := by
  apply lratCheckerSound f9143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9143
  · intro a ha; simp [p9143] at ha; subst a; trivial
  · exact checked9143
theorem derived9143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9143 := by
  apply localUnsat_implies_entails f9143 [c6956, c2754, c2783, c2887, c3346] c9143 unsat9143 (by rfl) a
  have h0 : Entails.eval a c6956 := derived6956 a h
  have h1 : Entails.eval a c2754 := h 2753 (by decide)
  have h2 : Entails.eval a c2783 := h 2782 (by decide)
  have h3 : Entails.eval a c2887 := h 2886 (by decide)
  have h4 : Entails.eval a c3346 := h 3345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9144 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3344, some c3409, some c3317, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9144 : lratChecker f9144 p9144 = .success := by decide +kernel
theorem unsat9144 : Unsatisfiable (PosFin 65) f9144 := by
  apply lratCheckerSound f9144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9144
  · intro a ha; simp [p9144] at ha; subst a; trivial
  · exact checked9144
theorem derived9144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9144 := by
  apply localUnsat_implies_entails f9144 [c3344, c3409, c3317] c9144 unsat9144 (by rfl) a
  have h0 : Entails.eval a c3344 := h 3343 (by decide)
  have h1 : Entails.eval a c3409 := h 3408 (by decide)
  have h2 : Entails.eval a c3317 := h 3316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9145 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c7129, some c9114, some c9130, some c9138, some c9141, some c9142, some c5734, some c5742, some c5348, some c5739, some c6956, some c5320, some c5199, some c5857, some c5740, some c4322, some c6988, some c3428, some c5210, some c5874, some c6913, some c3534, some c5264, some c5535, some c4464, some c9143, some c9090, some c9126, some c9144, some c2890, some c2845, some c3010, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked9145 : lratChecker f9145 p9145 = .success := by decide +kernel
theorem unsat9145 : Unsatisfiable (PosFin 65) f9145 := by
  apply lratCheckerSound f9145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9145
  · intro a ha; simp [p9145] at ha; subst a; trivial
  · exact checked9145
theorem derived9145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9145 := by
  apply localUnsat_implies_entails f9145 [c9064, c7129, c9114, c9130, c9138, c9141, c9142, c5734, c5742, c5348, c5739, c6956, c5320, c5199, c5857, c5740, c4322, c6988, c3428, c5210, c5874, c6913, c3534, c5264, c5535, c4464, c9143, c9090, c9126, c9144, c2890, c2845, c3010] c9145 unsat9145 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9114 := derived9114 a h
  have h3 : Entails.eval a c9130 := derived9130 a h
  have h4 : Entails.eval a c9138 := derived9138 a h
  have h5 : Entails.eval a c9141 := derived9141 a h
  have h6 : Entails.eval a c9142 := derived9142 a h
  have h7 : Entails.eval a c5734 := h 5733 (by decide)
  have h8 : Entails.eval a c5742 := h 5741 (by decide)
  have h9 : Entails.eval a c5348 := h 5347 (by decide)
  have h10 : Entails.eval a c5739 := h 5738 (by decide)
  have h11 : Entails.eval a c6956 := derived6956 a h
  have h12 : Entails.eval a c5320 := h 5319 (by decide)
  have h13 : Entails.eval a c5199 := h 5198 (by decide)
  have h14 : Entails.eval a c5857 := h 5856 (by decide)
  have h15 : Entails.eval a c5740 := h 5739 (by decide)
  have h16 : Entails.eval a c4322 := h 4321 (by decide)
  have h17 : Entails.eval a c6988 := derived6988 a h
  have h18 : Entails.eval a c3428 := h 3427 (by decide)
  have h19 : Entails.eval a c5210 := h 5209 (by decide)
  have h20 : Entails.eval a c5874 := h 5873 (by decide)
  have h21 : Entails.eval a c6913 := derived6913 a h
  have h22 : Entails.eval a c3534 := h 3533 (by decide)
  have h23 : Entails.eval a c5264 := h 5263 (by decide)
  have h24 : Entails.eval a c5535 := h 5534 (by decide)
  have h25 : Entails.eval a c4464 := h 4463 (by decide)
  have h26 : Entails.eval a c9143 := derived9143 a h
  have h27 : Entails.eval a c9090 := derived9090 a h
  have h28 : Entails.eval a c9126 := derived9126 a h
  have h29 : Entails.eval a c9144 := derived9144 a h
  have h30 : Entails.eval a c2890 := h 2889 (by decide)
  have h31 : Entails.eval a c2845 := h 2844 (by decide)
  have h32 : Entails.eval a c3010 := h 3009 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9146 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c9064, some c3911, some c5320, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9146 : lratChecker f9146 p9146 = .success := by decide +kernel
theorem unsat9146 : Unsatisfiable (PosFin 65) f9146 := by
  apply lratCheckerSound f9146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9146
  · intro a ha; simp [p9146] at ha; subst a; trivial
  · exact checked9146
theorem derived9146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9146 := by
  apply localUnsat_implies_entails f9146 [c9145, c9064, c3911, c5320] c9146 unsat9146 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c3911 := h 3910 (by decide)
  have h3 : Entails.eval a c5320 := h 5319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9147 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨45, by decide⟩, false), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9064, some c9119, some c5735, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9147 : lratChecker f9147 p9147 = .success := by decide +kernel
theorem unsat9147 : Unsatisfiable (PosFin 65) f9147 := by
  apply lratCheckerSound f9147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9147
  · intro a ha; simp [p9147] at ha; subst a; trivial
  · exact checked9147
theorem derived9147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9147 := by
  apply localUnsat_implies_entails f9147 [c9064, c9119, c5735] c9147 unsat9147 (by rfl) a
  have h0 : Entails.eval a c9064 := derived9064 a h
  have h1 : Entails.eval a c9119 := derived9119 a h
  have h2 : Entails.eval a c5735 := h 5734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9148 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c3672, some c9146, some c9064, some c6956, some c6798, some c6998, some c6805, some c7129, some c9147, some c5297, some c5734, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9148 : lratChecker f9148 p9148 = .success := by decide +kernel
theorem unsat9148 : Unsatisfiable (PosFin 65) f9148 := by
  apply lratCheckerSound f9148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9148
  · intro a ha; simp [p9148] at ha; subst a; trivial
  · exact checked9148
theorem derived9148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9148 := by
  apply localUnsat_implies_entails f9148 [c9145, c3672, c9146, c9064, c6956, c6798, c6998, c6805, c7129, c9147, c5297, c5734] c9148 unsat9148 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c3672 := h 3671 (by decide)
  have h2 : Entails.eval a c9146 := derived9146 a h
  have h3 : Entails.eval a c9064 := derived9064 a h
  have h4 : Entails.eval a c6956 := derived6956 a h
  have h5 : Entails.eval a c6798 := derived6798 a h
  have h6 : Entails.eval a c6998 := derived6998 a h
  have h7 : Entails.eval a c6805 := derived6805 a h
  have h8 : Entails.eval a c7129 := derived7129 a h
  have h9 : Entails.eval a c9147 := derived9147 a h
  have h10 : Entails.eval a c5297 := h 5296 (by decide)
  have h11 : Entails.eval a c5734 := h 5733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9149 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6730, some c6726, some c2759, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9149 : lratChecker f9149 p9149 = .success := by decide +kernel
theorem unsat9149 : Unsatisfiable (PosFin 65) f9149 := by
  apply lratCheckerSound f9149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9149
  · intro a ha; simp [p9149] at ha; subst a; trivial
  · exact checked9149
theorem derived9149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9149 := by
  apply localUnsat_implies_entails f9149 [c6730, c6726, c2759] c9149 unsat9149 (by rfl) a
  have h0 : Entails.eval a c6730 := derived6730 a h
  have h1 : Entails.eval a c6726 := derived6726 a h
  have h2 : Entails.eval a c2759 := h 2758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9150 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨63, by decide⟩, false), (⟨47, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2921, some c6734, some c2997, some c3178, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9150 : lratChecker f9150 p9150 = .success := by decide +kernel
theorem unsat9150 : Unsatisfiable (PosFin 65) f9150 := by
  apply lratCheckerSound f9150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9150
  · intro a ha; simp [p9150] at ha; subst a; trivial
  · exact checked9150
theorem derived9150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9150 := by
  apply localUnsat_implies_entails f9150 [c2921, c6734, c2997, c3178] c9150 unsat9150 (by rfl) a
  have h0 : Entails.eval a c2921 := h 2920 (by decide)
  have h1 : Entails.eval a c6734 := derived6734 a h
  have h2 : Entails.eval a c2997 := h 2996 (by decide)
  have h3 : Entails.eval a c3178 := h 3177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9151 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨47, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9149, some c9150, some c3340, some c3406, some c2755, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9151 : lratChecker f9151 p9151 = .success := by decide +kernel
theorem unsat9151 : Unsatisfiable (PosFin 65) f9151 := by
  apply lratCheckerSound f9151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9151
  · intro a ha; simp [p9151] at ha; subst a; trivial
  · exact checked9151
theorem derived9151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9151 := by
  apply localUnsat_implies_entails f9151 [c9149, c9150, c3340, c3406, c2755] c9151 unsat9151 (by rfl) a
  have h0 : Entails.eval a c9149 := derived9149 a h
  have h1 : Entails.eval a c9150 := derived9150 a h
  have h2 : Entails.eval a c3340 := h 3339 (by decide)
  have h3 : Entails.eval a c3406 := h 3405 (by decide)
  have h4 : Entails.eval a c2755 := h 2754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9152 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5759, some c5374, some c9151, some c2725, some c6719, some c6759, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9152 : lratChecker f9152 p9152 = .success := by decide +kernel
theorem unsat9152 : Unsatisfiable (PosFin 65) f9152 := by
  apply lratCheckerSound f9152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9152
  · intro a ha; simp [p9152] at ha; subst a; trivial
  · exact checked9152
theorem derived9152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9152 := by
  apply localUnsat_implies_entails f9152 [c5759, c5374, c9151, c2725, c6719, c6759] c9152 unsat9152 (by rfl) a
  have h0 : Entails.eval a c5759 := h 5758 (by decide)
  have h1 : Entails.eval a c5374 := h 5373 (by decide)
  have h2 : Entails.eval a c9151 := derived9151 a h
  have h3 : Entails.eval a c2725 := h 2724 (by decide)
  have h4 : Entails.eval a c6719 := derived6719 a h
  have h5 : Entails.eval a c6759 := derived6759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9153 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨63, by decide⟩, false), (⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6956, some c9119, some c6916, some c4223, some c6820, some c6835, some c5759, some c5374, some c9152, some c2711, some c2753, some c2783, some c3156, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9153 : lratChecker f9153 p9153 = .success := by decide +kernel
theorem unsat9153 : Unsatisfiable (PosFin 65) f9153 := by
  apply lratCheckerSound f9153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9153
  · intro a ha; simp [p9153] at ha; subst a; trivial
  · exact checked9153
theorem derived9153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9153 := by
  apply localUnsat_implies_entails f9153 [c6956, c9119, c6916, c4223, c6820, c6835, c5759, c5374, c9152, c2711, c2753, c2783, c3156] c9153 unsat9153 (by rfl) a
  have h0 : Entails.eval a c6956 := derived6956 a h
  have h1 : Entails.eval a c9119 := derived9119 a h
  have h2 : Entails.eval a c6916 := derived6916 a h
  have h3 : Entails.eval a c4223 := h 4222 (by decide)
  have h4 : Entails.eval a c6820 := derived6820 a h
  have h5 : Entails.eval a c6835 := derived6835 a h
  have h6 : Entails.eval a c5759 := h 5758 (by decide)
  have h7 : Entails.eval a c5374 := h 5373 (by decide)
  have h8 : Entails.eval a c9152 := derived9152 a h
  have h9 : Entails.eval a c2711 := h 2710 (by decide)
  have h10 : Entails.eval a c2753 := h 2752 (by decide)
  have h11 : Entails.eval a c2783 := h 2782 (by decide)
  have h12 : Entails.eval a c3156 := h 3155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9154 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨49, by decide⟩, true), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨40, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2711, some c2753, some c2783, some c3156, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9154 : lratChecker f9154 p9154 = .success := by decide +kernel
theorem unsat9154 : Unsatisfiable (PosFin 65) f9154 := by
  apply lratCheckerSound f9154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9154
  · intro a ha; simp [p9154] at ha; subst a; trivial
  · exact checked9154
theorem derived9154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9154 := by
  apply localUnsat_implies_entails f9154 [c2711, c2753, c2783, c3156] c9154 unsat9154 (by rfl) a
  have h0 : Entails.eval a c2711 := h 2710 (by decide)
  have h1 : Entails.eval a c2753 := h 2752 (by decide)
  have h2 : Entails.eval a c2783 := h 2782 (by decide)
  have h3 : Entails.eval a c3156 := h 3155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9155 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c9064, some c7129, some c3672, some c6956, some c6798, some c6998, some c6805, some c9146, some c9148, some c4223, some c9073, some c9072, some c6835, some c6820, some c9119, some c6916, some c9153, some c3917, some c6794, some c9103, some c9154, some c9045, some c9151, some c2725, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked9155 : lratChecker f9155 p9155 = .success := by decide +kernel
theorem unsat9155 : Unsatisfiable (PosFin 65) f9155 := by
  apply lratCheckerSound f9155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9155
  · intro a ha; simp [p9155] at ha; subst a; trivial
  · exact checked9155
theorem derived9155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9155 := by
  apply localUnsat_implies_entails f9155 [c9145, c9064, c7129, c3672, c6956, c6798, c6998, c6805, c9146, c9148, c4223, c9073, c9072, c6835, c6820, c9119, c6916, c9153, c3917, c6794, c9103, c9154, c9045, c9151, c2725] c9155 unsat9155 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c3672 := h 3671 (by decide)
  have h4 : Entails.eval a c6956 := derived6956 a h
  have h5 : Entails.eval a c6798 := derived6798 a h
  have h6 : Entails.eval a c6998 := derived6998 a h
  have h7 : Entails.eval a c6805 := derived6805 a h
  have h8 : Entails.eval a c9146 := derived9146 a h
  have h9 : Entails.eval a c9148 := derived9148 a h
  have h10 : Entails.eval a c4223 := h 4222 (by decide)
  have h11 : Entails.eval a c9073 := derived9073 a h
  have h12 : Entails.eval a c9072 := derived9072 a h
  have h13 : Entails.eval a c6835 := derived6835 a h
  have h14 : Entails.eval a c6820 := derived6820 a h
  have h15 : Entails.eval a c9119 := derived9119 a h
  have h16 : Entails.eval a c6916 := derived6916 a h
  have h17 : Entails.eval a c9153 := derived9153 a h
  have h18 : Entails.eval a c3917 := h 3916 (by decide)
  have h19 : Entails.eval a c6794 := derived6794 a h
  have h20 : Entails.eval a c9103 := derived9103 a h
  have h21 : Entails.eval a c9154 := derived9154 a h
  have h22 : Entails.eval a c9045 := derived9045 a h
  have h23 : Entails.eval a c9151 := derived9151 a h
  have h24 : Entails.eval a c2725 := h 2724 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9156 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c9064, some c6792, some c9070, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9156 : lratChecker f9156 p9156 = .success := by decide +kernel
theorem unsat9156 : Unsatisfiable (PosFin 65) f9156 := by
  apply lratCheckerSound f9156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9156
  · intro a ha; simp [p9156] at ha; subst a; trivial
  · exact checked9156
theorem derived9156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9156 := by
  apply localUnsat_implies_entails f9156 [c9145, c9064, c6792, c9070] c9156 unsat9156 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c6792 := derived6792 a h
  have h3 : Entails.eval a c9070 := derived9070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9157 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9155, some c9079, some c9145, some c9064, some c7129, some c3926, some c9156, some c3910, some c6434, some c9083, some c5298, some c9108, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9157 : lratChecker f9157 p9157 = .success := by decide +kernel
theorem unsat9157 : Unsatisfiable (PosFin 65) f9157 := by
  apply lratCheckerSound f9157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9157
  · intro a ha; simp [p9157] at ha; subst a; trivial
  · exact checked9157
theorem derived9157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9157 := by
  apply localUnsat_implies_entails f9157 [c9155, c9079, c9145, c9064, c7129, c3926, c9156, c3910, c6434, c9083, c5298, c9108] c9157 unsat9157 (by rfl) a
  have h0 : Entails.eval a c9155 := derived9155 a h
  have h1 : Entails.eval a c9079 := derived9079 a h
  have h2 : Entails.eval a c9145 := derived9145 a h
  have h3 : Entails.eval a c9064 := derived9064 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c3926 := h 3925 (by decide)
  have h6 : Entails.eval a c9156 := derived9156 a h
  have h7 : Entails.eval a c3910 := h 3909 (by decide)
  have h8 : Entails.eval a c6434 := derived6434 a h
  have h9 : Entails.eval a c9083 := derived9083 a h
  have h10 : Entails.eval a c5298 := h 5297 (by decide)
  have h11 : Entails.eval a c9108 := derived9108 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9158 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9155, some c9145, some c9064, some c7129, some c9157, some c9080, some c5314, some c5338, some c5319, some c6953, some c9074, some c3607, some c5284, some c3703, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9158 : lratChecker f9158 p9158 = .success := by decide +kernel
theorem unsat9158 : Unsatisfiable (PosFin 65) f9158 := by
  apply lratCheckerSound f9158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9158
  · intro a ha; simp [p9158] at ha; subst a; trivial
  · exact checked9158
theorem derived9158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9158 := by
  apply localUnsat_implies_entails f9158 [c9155, c9145, c9064, c7129, c9157, c9080, c5314, c5338, c5319, c6953, c9074, c3607, c5284, c3703] c9158 unsat9158 (by rfl) a
  have h0 : Entails.eval a c9155 := derived9155 a h
  have h1 : Entails.eval a c9145 := derived9145 a h
  have h2 : Entails.eval a c9064 := derived9064 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c9157 := derived9157 a h
  have h5 : Entails.eval a c9080 := derived9080 a h
  have h6 : Entails.eval a c5314 := h 5313 (by decide)
  have h7 : Entails.eval a c5338 := h 5337 (by decide)
  have h8 : Entails.eval a c5319 := h 5318 (by decide)
  have h9 : Entails.eval a c6953 := derived6953 a h
  have h10 : Entails.eval a c9074 := derived9074 a h
  have h11 : Entails.eval a c3607 := h 3606 (by decide)
  have h12 : Entails.eval a c5284 := h 5283 (by decide)
  have h13 : Entails.eval a c3703 := h 3702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9159 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c9064, some c7129, some c9155, some c9079, some c9158, some c3659, some c3661, some c9081, some c9108, some c7025, some c9115, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9159 : lratChecker f9159 p9159 = .success := by decide +kernel
theorem unsat9159 : Unsatisfiable (PosFin 65) f9159 := by
  apply lratCheckerSound f9159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9159
  · intro a ha; simp [p9159] at ha; subst a; trivial
  · exact checked9159
theorem derived9159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9159 := by
  apply localUnsat_implies_entails f9159 [c9145, c9064, c7129, c9155, c9079, c9158, c3659, c3661, c9081, c9108, c7025, c9115] c9159 unsat9159 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9155 := derived9155 a h
  have h4 : Entails.eval a c9079 := derived9079 a h
  have h5 : Entails.eval a c9158 := derived9158 a h
  have h6 : Entails.eval a c3659 := h 3658 (by decide)
  have h7 : Entails.eval a c3661 := h 3660 (by decide)
  have h8 : Entails.eval a c9081 := derived9081 a h
  have h9 : Entails.eval a c9108 := derived9108 a h
  have h10 : Entails.eval a c7025 := derived7025 a h
  have h11 : Entails.eval a c9115 := derived9115 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9160 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9159, some c9145, some c7129, some c3661, some c3667, some c3663, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9160 : lratChecker f9160 p9160 = .success := by decide +kernel
theorem unsat9160 : Unsatisfiable (PosFin 65) f9160 := by
  apply lratCheckerSound f9160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9160
  · intro a ha; simp [p9160] at ha; subst a; trivial
  · exact checked9160
theorem derived9160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9160 := by
  apply localUnsat_implies_entails f9160 [c9159, c9145, c7129, c3661, c3667, c3663] c9160 unsat9160 (by rfl) a
  have h0 : Entails.eval a c9159 := derived9159 a h
  have h1 : Entails.eval a c9145 := derived9145 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c3661 := h 3660 (by decide)
  have h4 : Entails.eval a c3667 := h 3666 (by decide)
  have h5 : Entails.eval a c3663 := h 3662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9161 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨38, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9079, some c9159, some c9145, some c9064, some c7129, some c6434, some c5304, some c5745, some c4215, some c9108, some c4111, some c3705, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9161 : lratChecker f9161 p9161 = .success := by decide +kernel
theorem unsat9161 : Unsatisfiable (PosFin 65) f9161 := by
  apply lratCheckerSound f9161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9161
  · intro a ha; simp [p9161] at ha; subst a; trivial
  · exact checked9161
theorem derived9161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9161 := by
  apply localUnsat_implies_entails f9161 [c9079, c9159, c9145, c9064, c7129, c6434, c5304, c5745, c4215, c9108, c4111, c3705] c9161 unsat9161 (by rfl) a
  have h0 : Entails.eval a c9079 := derived9079 a h
  have h1 : Entails.eval a c9159 := derived9159 a h
  have h2 : Entails.eval a c9145 := derived9145 a h
  have h3 : Entails.eval a c9064 := derived9064 a h
  have h4 : Entails.eval a c7129 := derived7129 a h
  have h5 : Entails.eval a c6434 := derived6434 a h
  have h6 : Entails.eval a c5304 := h 5303 (by decide)
  have h7 : Entails.eval a c5745 := h 5744 (by decide)
  have h8 : Entails.eval a c4215 := h 4214 (by decide)
  have h9 : Entails.eval a c9108 := derived9108 a h
  have h10 : Entails.eval a c4111 := h 4110 (by decide)
  have h11 : Entails.eval a c3705 := h 3704 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9162 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9145, some c9064, some c9160, some c9161, some c3910, some c5319, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9162 : lratChecker f9162 p9162 = .success := by decide +kernel
theorem unsat9162 : Unsatisfiable (PosFin 65) f9162 := by
  apply lratCheckerSound f9162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9162
  · intro a ha; simp [p9162] at ha; subst a; trivial
  · exact checked9162
theorem derived9162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9162 := by
  apply localUnsat_implies_entails f9162 [c9145, c9064, c9160, c9161, c3910, c5319] c9162 unsat9162 (by rfl) a
  have h0 : Entails.eval a c9145 := derived9145 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c9160 := derived9160 a h
  have h3 : Entails.eval a c9161 := derived9161 a h
  have h4 : Entails.eval a c3910 := h 3909 (by decide)
  have h5 : Entails.eval a c5319 := h 5318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9163 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9161, some c9162, some c9079, some c9159, some c9145, some c9064, some c7129, some c9080, some c5316, some c9074, some c5304, some c5745, some c3705, some c4123, some c6842, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9163 : lratChecker f9163 p9163 = .success := by decide +kernel
theorem unsat9163 : Unsatisfiable (PosFin 65) f9163 := by
  apply lratCheckerSound f9163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9163
  · intro a ha; simp [p9163] at ha; subst a; trivial
  · exact checked9163
theorem derived9163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9163 := by
  apply localUnsat_implies_entails f9163 [c9161, c9162, c9079, c9159, c9145, c9064, c7129, c9080, c5316, c9074, c5304, c5745, c3705, c4123, c6842] c9163 unsat9163 (by rfl) a
  have h0 : Entails.eval a c9161 := derived9161 a h
  have h1 : Entails.eval a c9162 := derived9162 a h
  have h2 : Entails.eval a c9079 := derived9079 a h
  have h3 : Entails.eval a c9159 := derived9159 a h
  have h4 : Entails.eval a c9145 := derived9145 a h
  have h5 : Entails.eval a c9064 := derived9064 a h
  have h6 : Entails.eval a c7129 := derived7129 a h
  have h7 : Entails.eval a c9080 := derived9080 a h
  have h8 : Entails.eval a c5316 := h 5315 (by decide)
  have h9 : Entails.eval a c9074 := derived9074 a h
  have h10 : Entails.eval a c5304 := h 5303 (by decide)
  have h11 : Entails.eval a c5745 := h 5744 (by decide)
  have h12 : Entails.eval a c3705 := h 3704 (by decide)
  have h13 : Entails.eval a c4123 := h 4122 (by decide)
  have h14 : Entails.eval a c6842 := derived6842 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9164 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9162, some c9145, some c7129, some c3926, some c9156, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9164 : lratChecker f9164 p9164 = .success := by decide +kernel
theorem unsat9164 : Unsatisfiable (PosFin 65) f9164 := by
  apply lratCheckerSound f9164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9164
  · intro a ha; simp [p9164] at ha; subst a; trivial
  · exact checked9164
theorem derived9164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9164 := by
  apply localUnsat_implies_entails f9164 [c9162, c9145, c7129, c3926, c9156] c9164 unsat9164 (by rfl) a
  have h0 : Entails.eval a c9162 := derived9162 a h
  have h1 : Entails.eval a c9145 := derived9145 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c3926 := h 3925 (by decide)
  have h4 : Entails.eval a c9156 := derived9156 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9165 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9159, some c9145, some c7129, some c9162, some c9164, some c9163, some c3667, some c3657, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9165 : lratChecker f9165 p9165 = .success := by decide +kernel
theorem unsat9165 : Unsatisfiable (PosFin 65) f9165 := by
  apply lratCheckerSound f9165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9165
  · intro a ha; simp [p9165] at ha; subst a; trivial
  · exact checked9165
theorem derived9165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9165 := by
  apply localUnsat_implies_entails f9165 [c9159, c9145, c7129, c9162, c9164, c9163, c3667, c3657] c9165 unsat9165 (by rfl) a
  have h0 : Entails.eval a c9159 := derived9159 a h
  have h1 : Entails.eval a c9145 := derived9145 a h
  have h2 : Entails.eval a c7129 := derived7129 a h
  have h3 : Entails.eval a c9162 := derived9162 a h
  have h4 : Entails.eval a c9164 := derived9164 a h
  have h5 : Entails.eval a c9163 := derived9163 a h
  have h6 : Entails.eval a c3667 := h 3666 (by decide)
  have h7 : Entails.eval a c3657 := h 3656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9166 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9165, some c9159, some c9145, some c7129, some c3662, some c3667, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9166 : lratChecker f9166 p9166 = .success := by decide +kernel
theorem unsat9166 : Unsatisfiable (PosFin 65) f9166 := by
  apply lratCheckerSound f9166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9166
  · intro a ha; simp [p9166] at ha; subst a; trivial
  · exact checked9166
theorem derived9166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9166 := by
  apply localUnsat_implies_entails f9166 [c9165, c9159, c9145, c7129, c3662, c3667] c9166 unsat9166 (by rfl) a
  have h0 : Entails.eval a c9165 := derived9165 a h
  have h1 : Entails.eval a c9159 := derived9159 a h
  have h2 : Entails.eval a c9145 := derived9145 a h
  have h3 : Entails.eval a c7129 := derived7129 a h
  have h4 : Entails.eval a c3662 := h 3661 (by decide)
  have h5 : Entails.eval a c3667 := h 3666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9167 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false), (⟨57, by decide⟩, false), (⟨63, by decide⟩, false), (⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2726, some c2793, some c3235, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9167 : lratChecker f9167 p9167 = .success := by decide +kernel
theorem unsat9167 : Unsatisfiable (PosFin 65) f9167 := by
  apply lratCheckerSound f9167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9167
  · intro a ha; simp [p9167] at ha; subst a; trivial
  · exact checked9167
theorem derived9167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9167 := by
  apply localUnsat_implies_entails f9167 [c2726, c2793, c3235] c9167 unsat9167 (by rfl) a
  have h0 : Entails.eval a c2726 := h 2725 (by decide)
  have h1 : Entails.eval a c2793 := h 2792 (by decide)
  have h2 : Entails.eval a c3235 := h 3234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9168 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, false), (⟨47, by decide⟩, false), (⟨38, by decide⟩, false), (⟨62, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3216, some c3235, some c3239, some c3357, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true))]
def p9168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9168 : lratChecker f9168 p9168 = .success := by decide +kernel
theorem unsat9168 : Unsatisfiable (PosFin 65) f9168 := by
  apply lratCheckerSound f9168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9168
  · intro a ha; simp [p9168] at ha; subst a; trivial
  · exact checked9168
theorem derived9168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9168 := by
  apply localUnsat_implies_entails f9168 [c3216, c3235, c3239, c3357] c9168 unsat9168 (by rfl) a
  have h0 : Entails.eval a c3216 := h 3215 (by decide)
  have h1 : Entails.eval a c3235 := h 3234 (by decide)
  have h2 : Entails.eval a c3239 := h 3238 (by decide)
  have h3 : Entails.eval a c3357 := h 3356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9169 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨42, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, false), (⟨46, by decide⟩, false), (⟨63, by decide⟩, false), (⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨38, by decide⟩, false), (⟨62, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9167, some c9168, some c2734, some c2863, some c3187, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9169 : lratChecker f9169 p9169 = .success := by decide +kernel
theorem unsat9169 : Unsatisfiable (PosFin 65) f9169 := by
  apply lratCheckerSound f9169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9169
  · intro a ha; simp [p9169] at ha; subst a; trivial
  · exact checked9169
theorem derived9169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9169 := by
  apply localUnsat_implies_entails f9169 [c9167, c9168, c2734, c2863, c3187] c9169 unsat9169 (by rfl) a
  have h0 : Entails.eval a c9167 := derived9167 a h
  have h1 : Entails.eval a c9168 := derived9168 a h
  have h2 : Entails.eval a c2734 := h 2733 (by decide)
  have h3 : Entails.eval a c2863 := h 2862 (by decide)
  have h4 : Entails.eval a c3187 := h 3186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9170 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9064, some c9165, some c9166, some c9146, some c9159, some c9145, some c4985, some c3612, some c5304, some c4677, some c4000, some c9072, some c9073, some c5287, some c3705, some c5745, some c7029, some c5328, some c7033, some c7032, some c4027, some c9169, some c2880, some c2781, some c2865, some c3154, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked9170 : lratChecker f9170 p9170 = .success := by decide +kernel
theorem unsat9170 : Unsatisfiable (PosFin 65) f9170 := by
  apply lratCheckerSound f9170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9170
  · intro a ha; simp [p9170] at ha; subst a; trivial
  · exact checked9170
theorem derived9170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9170 := by
  apply localUnsat_implies_entails f9170 [c7129, c9064, c9165, c9166, c9146, c9159, c9145, c4985, c3612, c5304, c4677, c4000, c9072, c9073, c5287, c3705, c5745, c7029, c5328, c7033, c7032, c4027, c9169, c2880, c2781, c2865, c3154] c9170 unsat9170 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c9165 := derived9165 a h
  have h3 : Entails.eval a c9166 := derived9166 a h
  have h4 : Entails.eval a c9146 := derived9146 a h
  have h5 : Entails.eval a c9159 := derived9159 a h
  have h6 : Entails.eval a c9145 := derived9145 a h
  have h7 : Entails.eval a c4985 := h 4984 (by decide)
  have h8 : Entails.eval a c3612 := h 3611 (by decide)
  have h9 : Entails.eval a c5304 := h 5303 (by decide)
  have h10 : Entails.eval a c4677 := h 4676 (by decide)
  have h11 : Entails.eval a c4000 := h 3999 (by decide)
  have h12 : Entails.eval a c9072 := derived9072 a h
  have h13 : Entails.eval a c9073 := derived9073 a h
  have h14 : Entails.eval a c5287 := h 5286 (by decide)
  have h15 : Entails.eval a c3705 := h 3704 (by decide)
  have h16 : Entails.eval a c5745 := h 5744 (by decide)
  have h17 : Entails.eval a c7029 := derived7029 a h
  have h18 : Entails.eval a c5328 := h 5327 (by decide)
  have h19 : Entails.eval a c7033 := derived7033 a h
  have h20 : Entails.eval a c7032 := derived7032 a h
  have h21 : Entails.eval a c4027 := h 4026 (by decide)
  have h22 : Entails.eval a c9169 := derived9169 a h
  have h23 : Entails.eval a c2880 := h 2879 (by decide)
  have h24 : Entails.eval a c2781 := h 2780 (by decide)
  have h25 : Entails.eval a c2865 := h 2864 (by decide)
  have h26 : Entails.eval a c3154 := h 3153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9171 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨46, by decide⟩, true), (⟨63, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, true), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2864, some c2882, some c2781, some c3157, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p9171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9171 : lratChecker f9171 p9171 = .success := by decide +kernel
theorem unsat9171 : Unsatisfiable (PosFin 65) f9171 := by
  apply lratCheckerSound f9171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9171
  · intro a ha; simp [p9171] at ha; subst a; trivial
  · exact checked9171
theorem derived9171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9171 := by
  apply localUnsat_implies_entails f9171 [c2864, c2882, c2781, c3157] c9171 unsat9171 (by rfl) a
  have h0 : Entails.eval a c2864 := h 2863 (by decide)
  have h1 : Entails.eval a c2882 := h 2881 (by decide)
  have h2 : Entails.eval a c2781 := h 2780 (by decide)
  have h3 : Entails.eval a c3157 := h 3156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9172 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9064, some c9165, some c9166, some c9146, some c9159, some c9145, some c4985, some c3612, some c5304, some c4677, some c4000, some c9072, some c9073, some c5287, some c3705, some c5745, some c3917, some c6839, some c6836, some c5222, some c6837, some c6635, some c4448, some c4027, some c3928, some c4482, some c9171, some c9045, some c9167, some c2867, some c2862, some c3188, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked9172 : lratChecker f9172 p9172 = .success := by decide +kernel
theorem unsat9172 : Unsatisfiable (PosFin 65) f9172 := by
  apply lratCheckerSound f9172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9172
  · intro a ha; simp [p9172] at ha; subst a; trivial
  · exact checked9172
theorem derived9172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9172 := by
  apply localUnsat_implies_entails f9172 [c7129, c9064, c9165, c9166, c9146, c9159, c9145, c4985, c3612, c5304, c4677, c4000, c9072, c9073, c5287, c3705, c5745, c3917, c6839, c6836, c5222, c6837, c6635, c4448, c4027, c3928, c4482, c9171, c9045, c9167, c2867, c2862, c3188] c9172 unsat9172 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c9165 := derived9165 a h
  have h3 : Entails.eval a c9166 := derived9166 a h
  have h4 : Entails.eval a c9146 := derived9146 a h
  have h5 : Entails.eval a c9159 := derived9159 a h
  have h6 : Entails.eval a c9145 := derived9145 a h
  have h7 : Entails.eval a c4985 := h 4984 (by decide)
  have h8 : Entails.eval a c3612 := h 3611 (by decide)
  have h9 : Entails.eval a c5304 := h 5303 (by decide)
  have h10 : Entails.eval a c4677 := h 4676 (by decide)
  have h11 : Entails.eval a c4000 := h 3999 (by decide)
  have h12 : Entails.eval a c9072 := derived9072 a h
  have h13 : Entails.eval a c9073 := derived9073 a h
  have h14 : Entails.eval a c5287 := h 5286 (by decide)
  have h15 : Entails.eval a c3705 := h 3704 (by decide)
  have h16 : Entails.eval a c5745 := h 5744 (by decide)
  have h17 : Entails.eval a c3917 := h 3916 (by decide)
  have h18 : Entails.eval a c6839 := derived6839 a h
  have h19 : Entails.eval a c6836 := derived6836 a h
  have h20 : Entails.eval a c5222 := h 5221 (by decide)
  have h21 : Entails.eval a c6837 := derived6837 a h
  have h22 : Entails.eval a c6635 := derived6635 a h
  have h23 : Entails.eval a c4448 := h 4447 (by decide)
  have h24 : Entails.eval a c4027 := h 4026 (by decide)
  have h25 : Entails.eval a c3928 := h 3927 (by decide)
  have h26 : Entails.eval a c4482 := h 4481 (by decide)
  have h27 : Entails.eval a c9171 := derived9171 a h
  have h28 : Entails.eval a c9045 := derived9045 a h
  have h29 : Entails.eval a c9167 := derived9167 a h
  have h30 : Entails.eval a c2867 := h 2866 (by decide)
  have h31 : Entails.eval a c2862 := h 2861 (by decide)
  have h32 : Entails.eval a c3188 := h 3187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9173 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7129, some c9064, some c9145, some c9159, some c9165, some c9166, some c9146, some c5304, some c4985, some c3612, some c4677, some c4000, some c9073, some c9172, some c5328, some c9170, some c5317, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9173 : lratChecker f9173 p9173 = .success := by decide +kernel
theorem unsat9173 : Unsatisfiable (PosFin 65) f9173 := by
  apply lratCheckerSound f9173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9173
  · intro a ha; simp [p9173] at ha; subst a; trivial
  · exact checked9173
theorem derived9173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9173 := by
  apply localUnsat_implies_entails f9173 [c7129, c9064, c9145, c9159, c9165, c9166, c9146, c5304, c4985, c3612, c4677, c4000, c9073, c9172, c5328, c9170, c5317] c9173 unsat9173 (by rfl) a
  have h0 : Entails.eval a c7129 := derived7129 a h
  have h1 : Entails.eval a c9064 := derived9064 a h
  have h2 : Entails.eval a c9145 := derived9145 a h
  have h3 : Entails.eval a c9159 := derived9159 a h
  have h4 : Entails.eval a c9165 := derived9165 a h
  have h5 : Entails.eval a c9166 := derived9166 a h
  have h6 : Entails.eval a c9146 := derived9146 a h
  have h7 : Entails.eval a c5304 := h 5303 (by decide)
  have h8 : Entails.eval a c4985 := h 4984 (by decide)
  have h9 : Entails.eval a c3612 := h 3611 (by decide)
  have h10 : Entails.eval a c4677 := h 4676 (by decide)
  have h11 : Entails.eval a c4000 := h 3999 (by decide)
  have h12 : Entails.eval a c9073 := derived9073 a h
  have h13 : Entails.eval a c9172 := derived9172 a h
  have h14 : Entails.eval a c5328 := h 5327 (by decide)
  have h15 : Entails.eval a c9170 := derived9170 a h
  have h16 : Entails.eval a c5317 := h 5316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9174 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c4556, some c4606, some c5657, some c5586, some c4945, some c4760, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9174 : lratChecker f9174 p9174 = .success := by decide +kernel
theorem unsat9174 : Unsatisfiable (PosFin 65) f9174 := by
  apply lratCheckerSound f9174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9174
  · intro a ha; simp [p9174] at ha; subst a; trivial
  · exact checked9174
theorem derived9174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9174 := by
  apply localUnsat_implies_entails f9174 [c9173, c7129, c4556, c4606, c5657, c5586, c4945, c4760] c9174 unsat9174 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c4556 := h 4555 (by decide)
  have h3 : Entails.eval a c4606 := h 4605 (by decide)
  have h4 : Entails.eval a c5657 := h 5656 (by decide)
  have h5 : Entails.eval a c5586 := h 5585 (by decide)
  have h6 : Entails.eval a c4945 := h 4944 (by decide)
  have h7 : Entails.eval a c4760 := h 4759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9175 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨35, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c4905, some c4945, some c4629, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9175 : lratChecker f9175 p9175 = .success := by decide +kernel
theorem unsat9175 : Unsatisfiable (PosFin 65) f9175 := by
  apply lratCheckerSound f9175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9175
  · intro a ha; simp [p9175] at ha; subst a; trivial
  · exact checked9175
theorem derived9175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9175 := by
  apply localUnsat_implies_entails f9175 [c9173, c7129, c4905, c4945, c4629] c9175 unsat9175 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c4905 := h 4904 (by decide)
  have h3 : Entails.eval a c4945 := h 4944 (by decide)
  have h4 : Entails.eval a c4629 := h 4628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9176 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c9174, some c9175, some c4796, some c4738, some c5759, some c5584, some c4629, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9176 : lratChecker f9176 p9176 = .success := by decide +kernel
theorem unsat9176 : Unsatisfiable (PosFin 65) f9176 := by
  apply lratCheckerSound f9176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9176
  · intro a ha; simp [p9176] at ha; subst a; trivial
  · exact checked9176
theorem derived9176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9176 := by
  apply localUnsat_implies_entails f9176 [c9173, c7129, c9174, c9175, c4796, c4738, c5759, c5584, c4629] c9176 unsat9176 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c9174 := derived9174 a h
  have h3 : Entails.eval a c9175 := derived9175 a h
  have h4 : Entails.eval a c4796 := h 4795 (by decide)
  have h5 : Entails.eval a c4738 := h 4737 (by decide)
  have h6 : Entails.eval a c5759 := h 5758 (by decide)
  have h7 : Entails.eval a c5584 := h 5583 (by decide)
  have h8 : Entails.eval a c4629 := h 4628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9177 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6906, some c4640, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p9177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9177 : lratChecker f9177 p9177 = .success := by decide +kernel
theorem unsat9177 : Unsatisfiable (PosFin 65) f9177 := by
  apply lratCheckerSound f9177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9177
  · intro a ha; simp [p9177] at ha; subst a; trivial
  · exact checked9177
theorem derived9177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9177 := by
  apply localUnsat_implies_entails f9177 [c6906, c4640] c9177 unsat9177 (by rfl) a
  have h0 : Entails.eval a c6906 := derived6906 a h
  have h1 : Entails.eval a c4640 := h 4639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9178 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c4905, some c5092, some c5695, some c4677, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9178 : lratChecker f9178 p9178 = .success := by decide +kernel
theorem unsat9178 : Unsatisfiable (PosFin 65) f9178 := by
  apply lratCheckerSound f9178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9178
  · intro a ha; simp [p9178] at ha; subst a; trivial
  · exact checked9178
theorem derived9178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9178 := by
  apply localUnsat_implies_entails f9178 [c9173, c7129, c4905, c5092, c5695, c4677] c9178 unsat9178 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c4905 := h 4904 (by decide)
  have h3 : Entails.eval a c5092 := h 5091 (by decide)
  have h4 : Entails.eval a c5695 := h 5694 (by decide)
  have h5 : Entails.eval a c4677 := h 4676 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9179 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨51, by decide⟩, false), (⟨62, by decide⟩, false), (⟨58, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5847, some c4945, some c5584, some c4760, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p9179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9179 : lratChecker f9179 p9179 = .success := by decide +kernel
theorem unsat9179 : Unsatisfiable (PosFin 65) f9179 := by
  apply lratCheckerSound f9179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9179
  · intro a ha; simp [p9179] at ha; subst a; trivial
  · exact checked9179
theorem derived9179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9179 := by
  apply localUnsat_implies_entails f9179 [c5847, c4945, c5584, c4760] c9179 unsat9179 (by rfl) a
  have h0 : Entails.eval a c5847 := h 5846 (by decide)
  have h1 : Entails.eval a c4945 := h 4944 (by decide)
  have h2 : Entails.eval a c5584 := h 5583 (by decide)
  have h3 : Entails.eval a c4760 := h 4759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9180 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, false), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9173, some c7129, some c4619, some c6790, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9180 : lratChecker f9180 p9180 = .success := by decide +kernel
theorem unsat9180 : Unsatisfiable (PosFin 65) f9180 := by
  apply lratCheckerSound f9180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9180
  · intro a ha; simp [p9180] at ha; subst a; trivial
  · exact checked9180
theorem derived9180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9180 := by
  apply localUnsat_implies_entails f9180 [c9173, c7129, c4619, c6790] c9180 unsat9180 (by rfl) a
  have h0 : Entails.eval a c9173 := derived9173 a h
  have h1 : Entails.eval a c7129 := derived7129 a h
  have h2 : Entails.eval a c4619 := h 4618 (by decide)
  have h3 : Entails.eval a c6790 := derived6790 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9180

end CochromaticTwenty.Certificates.FixedCore1
