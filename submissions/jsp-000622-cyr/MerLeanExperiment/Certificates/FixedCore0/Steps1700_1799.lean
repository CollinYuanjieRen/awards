import MerLeanExperiment.Certificates.FixedCore0.Steps1600_1699

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9251 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9251 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3213, some c3223, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9251 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9251 : lratChecker f9251 p9251 = .success := by decide +kernel
theorem unsat9251 : Unsatisfiable (PosFin 65) f9251 := by
  apply lratCheckerSound f9251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9251
  · intro a ha; simp [p9251] at ha; subst a; trivial
  · exact checked9251
theorem derived9251 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9251 := by
  apply localUnsat_implies_entails f9251 [c3213, c3223] c9251 unsat9251 (by rfl) a
  have h0 : Entails.eval a c3213 := h 3212 (by decide)
  have h1 : Entails.eval a c3223 := h 3222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9252 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9252 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9251, some c3328, some c3295, some c3356, some c779, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9252 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9252 : lratChecker f9252 p9252 = .success := by decide +kernel
theorem unsat9252 : Unsatisfiable (PosFin 65) f9252 := by
  apply lratCheckerSound f9252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9252
  · intro a ha; simp [p9252] at ha; subst a; trivial
  · exact checked9252
theorem derived9252 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9252 := by
  apply localUnsat_implies_entails f9252 [c9251, c3328, c3295, c3356, c779] c9252 unsat9252 (by rfl) a
  have h0 : Entails.eval a c9251 := derived9251 a h
  have h1 : Entails.eval a c3328 := h 3327 (by decide)
  have h2 : Entails.eval a c3295 := h 3294 (by decide)
  have h3 : Entails.eval a c3356 := h 3355 (by decide)
  have h4 : Entails.eval a c779 := h 778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9253 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9253 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9178, some c9193, some c9195, some c8580, some c9251, some c9252, some c3624, some c3653, some c779, some c5484, some c5498, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9253 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9253 : lratChecker f9253 p9253 = .success := by decide +kernel
theorem unsat9253 : Unsatisfiable (PosFin 65) f9253 := by
  apply lratCheckerSound f9253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9253
  · intro a ha; simp [p9253] at ha; subst a; trivial
  · exact checked9253
theorem derived9253 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9253 := by
  apply localUnsat_implies_entails f9253 [c9178, c9193, c9195, c8580, c9251, c9252, c3624, c3653, c779, c5484, c5498] c9253 unsat9253 (by rfl) a
  have h0 : Entails.eval a c9178 := derived9178 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9195 := derived9195 a h
  have h3 : Entails.eval a c8580 := derived8580 a h
  have h4 : Entails.eval a c9251 := derived9251 a h
  have h5 : Entails.eval a c9252 := derived9252 a h
  have h6 : Entails.eval a c3624 := h 3623 (by decide)
  have h7 : Entails.eval a c3653 := h 3652 (by decide)
  have h8 : Entails.eval a c779 := h 778 (by decide)
  have h9 : Entails.eval a c5484 := h 5483 (by decide)
  have h10 : Entails.eval a c5498 := h 5497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9254 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨62, by decide⟩, false), (⟨63, by decide⟩, true), (⟨58, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9254 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3357, some c3346, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9254 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9254 : lratChecker f9254 p9254 = .success := by decide +kernel
theorem unsat9254 : Unsatisfiable (PosFin 65) f9254 := by
  apply lratCheckerSound f9254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9254
  · intro a ha; simp [p9254] at ha; subst a; trivial
  · exact checked9254
theorem derived9254 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9254 := by
  apply localUnsat_implies_entails f9254 [c3357, c3346] c9254 unsat9254 (by rfl) a
  have h0 : Entails.eval a c3357 := h 3356 (by decide)
  have h1 : Entails.eval a c3346 := h 3345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9255 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨8, by decide⟩, true), (⟨58, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9255 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1433, some c1378, some c4913, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9255 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9255 : lratChecker f9255 p9255 = .success := by decide +kernel
theorem unsat9255 : Unsatisfiable (PosFin 65) f9255 := by
  apply lratCheckerSound f9255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9255
  · intro a ha; simp [p9255] at ha; subst a; trivial
  · exact checked9255
theorem derived9255 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9255 := by
  apply localUnsat_implies_entails f9255 [c1433, c1378, c4913] c9255 unsat9255 (by rfl) a
  have h0 : Entails.eval a c1433 := h 1432 (by decide)
  have h1 : Entails.eval a c1378 := h 1377 (by decide)
  have h2 : Entails.eval a c4913 := h 4912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9256 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9256 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3235, some c3251, some c3247, some c3255, some c3254, some c9254, some c9255, some c1372, some c4937, some c1428, some c4462, some c4520, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9256 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9256 : lratChecker f9256 p9256 = .success := by decide +kernel
theorem unsat9256 : Unsatisfiable (PosFin 65) f9256 := by
  apply lratCheckerSound f9256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9256
  · intro a ha; simp [p9256] at ha; subst a; trivial
  · exact checked9256
theorem derived9256 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9256 := by
  apply localUnsat_implies_entails f9256 [c3235, c3251, c3247, c3255, c3254, c9254, c9255, c1372, c4937, c1428, c4462, c4520] c9256 unsat9256 (by rfl) a
  have h0 : Entails.eval a c3235 := h 3234 (by decide)
  have h1 : Entails.eval a c3251 := h 3250 (by decide)
  have h2 : Entails.eval a c3247 := h 3246 (by decide)
  have h3 : Entails.eval a c3255 := h 3254 (by decide)
  have h4 : Entails.eval a c3254 := h 3253 (by decide)
  have h5 : Entails.eval a c9254 := derived9254 a h
  have h6 : Entails.eval a c9255 := derived9255 a h
  have h7 : Entails.eval a c1372 := h 1371 (by decide)
  have h8 : Entails.eval a c4937 := h 4936 (by decide)
  have h9 : Entails.eval a c1428 := h 1427 (by decide)
  have h10 : Entails.eval a c4462 := h 4461 (by decide)
  have h11 : Entails.eval a c4520 := h 4519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9257 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9257 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3326, some c3344, some c3339, some c3345, some c3357, some c3346, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9257 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9257 : lratChecker f9257 p9257 = .success := by decide +kernel
theorem unsat9257 : Unsatisfiable (PosFin 65) f9257 := by
  apply lratCheckerSound f9257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9257
  · intro a ha; simp [p9257] at ha; subst a; trivial
  · exact checked9257
theorem derived9257 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9257 := by
  apply localUnsat_implies_entails f9257 [c3326, c3344, c3339, c3345, c3357, c3346] c9257 unsat9257 (by rfl) a
  have h0 : Entails.eval a c3326 := h 3325 (by decide)
  have h1 : Entails.eval a c3344 := h 3343 (by decide)
  have h2 : Entails.eval a c3339 := h 3338 (by decide)
  have h3 : Entails.eval a c3345 := h 3344 (by decide)
  have h4 : Entails.eval a c3357 := h 3356 (by decide)
  have h5 : Entails.eval a c3346 := h 3345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9258 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9258 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9218, some c9193, some c9244, some c9250, some c9253, some c9256, some c9257, some c3631, some c3630, some c3663, some c2787, some c4043, some c3644, some c4258, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9258 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9258 : lratChecker f9258 p9258 = .success := by decide +kernel
theorem unsat9258 : Unsatisfiable (PosFin 65) f9258 := by
  apply lratCheckerSound f9258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9258
  · intro a ha; simp [p9258] at ha; subst a; trivial
  · exact checked9258
theorem derived9258 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9258 := by
  apply localUnsat_implies_entails f9258 [c9218, c9193, c9244, c9250, c9253, c9256, c9257, c3631, c3630, c3663, c2787, c4043, c3644, c4258] c9258 unsat9258 (by rfl) a
  have h0 : Entails.eval a c9218 := derived9218 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9244 := derived9244 a h
  have h3 : Entails.eval a c9250 := derived9250 a h
  have h4 : Entails.eval a c9253 := derived9253 a h
  have h5 : Entails.eval a c9256 := derived9256 a h
  have h6 : Entails.eval a c9257 := derived9257 a h
  have h7 : Entails.eval a c3631 := h 3630 (by decide)
  have h8 : Entails.eval a c3630 := h 3629 (by decide)
  have h9 : Entails.eval a c3663 := h 3662 (by decide)
  have h10 : Entails.eval a c2787 := h 2786 (by decide)
  have h11 : Entails.eval a c4043 := h 4042 (by decide)
  have h12 : Entails.eval a c3644 := h 3643 (by decide)
  have h13 : Entails.eval a c4258 := h 4257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9259 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9259 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2810, some c2613, some c4489, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9259 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9259 : lratChecker f9259 p9259 = .success := by decide +kernel
theorem unsat9259 : Unsatisfiable (PosFin 65) f9259 := by
  apply lratCheckerSound f9259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9259
  · intro a ha; simp [p9259] at ha; subst a; trivial
  · exact checked9259
theorem derived9259 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9259 := by
  apply localUnsat_implies_entails f9259 [c2810, c2613, c4489] c9259 unsat9259 (by rfl) a
  have h0 : Entails.eval a c2810 := h 2809 (by decide)
  have h1 : Entails.eval a c2613 := h 2612 (by decide)
  have h2 : Entails.eval a c4489 := h 4488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9260 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9260 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9258, some c9218, some c9193, some c9259, some c1094, some c9147, some c1091, some c1090, some c9178, some c1108, some c1115, some c9195, some c8496, some c8580, some c8846, some c1066, some c8840, some c685, some c8609, some c1069, some c8583, some c594, some c9050, some c3103, some c3100, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9260 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked9260 : lratChecker f9260 p9260 = .success := by decide +kernel
theorem unsat9260 : Unsatisfiable (PosFin 65) f9260 := by
  apply lratCheckerSound f9260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9260
  · intro a ha; simp [p9260] at ha; subst a; trivial
  · exact checked9260
theorem derived9260 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9260 := by
  apply localUnsat_implies_entails f9260 [c9258, c9218, c9193, c9259, c1094, c9147, c1091, c1090, c9178, c1108, c1115, c9195, c8496, c8580, c8846, c1066, c8840, c685, c8609, c1069, c8583, c594, c9050, c3103, c3100] c9260 unsat9260 (by rfl) a
  have h0 : Entails.eval a c9258 := derived9258 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9259 := derived9259 a h
  have h4 : Entails.eval a c1094 := h 1093 (by decide)
  have h5 : Entails.eval a c9147 := derived9147 a h
  have h6 : Entails.eval a c1091 := h 1090 (by decide)
  have h7 : Entails.eval a c1090 := h 1089 (by decide)
  have h8 : Entails.eval a c9178 := derived9178 a h
  have h9 : Entails.eval a c1108 := h 1107 (by decide)
  have h10 : Entails.eval a c1115 := h 1114 (by decide)
  have h11 : Entails.eval a c9195 := derived9195 a h
  have h12 : Entails.eval a c8496 := derived8496 a h
  have h13 : Entails.eval a c8580 := derived8580 a h
  have h14 : Entails.eval a c8846 := derived8846 a h
  have h15 : Entails.eval a c1066 := h 1065 (by decide)
  have h16 : Entails.eval a c8840 := derived8840 a h
  have h17 : Entails.eval a c685 := h 684 (by decide)
  have h18 : Entails.eval a c8609 := derived8609 a h
  have h19 : Entails.eval a c1069 := h 1068 (by decide)
  have h20 : Entails.eval a c8583 := derived8583 a h
  have h21 : Entails.eval a c594 := h 593 (by decide)
  have h22 : Entails.eval a c9050 := derived9050 a h
  have h23 : Entails.eval a c3103 := h 3102 (by decide)
  have h24 : Entails.eval a c3100 := h 3099 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9261 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9261 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1089, some c1096, some c1102, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9261 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9261 : lratChecker f9261 p9261 = .success := by decide +kernel
theorem unsat9261 : Unsatisfiable (PosFin 65) f9261 := by
  apply lratCheckerSound f9261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9261
  · intro a ha; simp [p9261] at ha; subst a; trivial
  · exact checked9261
theorem derived9261 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9261 := by
  apply localUnsat_implies_entails f9261 [c1089, c1096, c1102] c9261 unsat9261 (by rfl) a
  have h0 : Entails.eval a c1089 := h 1088 (by decide)
  have h1 : Entails.eval a c1096 := h 1095 (by decide)
  have h2 : Entails.eval a c1102 := h 1101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9262 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9262 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9261, some c1091, some c1090, some c1101, some c1093, some c1095, some c1113, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9262 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9262 : lratChecker f9262 p9262 = .success := by decide +kernel
theorem unsat9262 : Unsatisfiable (PosFin 65) f9262 := by
  apply lratCheckerSound f9262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9262
  · intro a ha; simp [p9262] at ha; subst a; trivial
  · exact checked9262
theorem derived9262 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9262 := by
  apply localUnsat_implies_entails f9262 [c9261, c1091, c1090, c1101, c1093, c1095, c1113] c9262 unsat9262 (by rfl) a
  have h0 : Entails.eval a c9261 := derived9261 a h
  have h1 : Entails.eval a c1091 := h 1090 (by decide)
  have h2 : Entails.eval a c1090 := h 1089 (by decide)
  have h3 : Entails.eval a c1101 := h 1100 (by decide)
  have h4 : Entails.eval a c1093 := h 1092 (by decide)
  have h5 : Entails.eval a c1095 := h 1094 (by decide)
  have h6 : Entails.eval a c1113 := h 1112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9263 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9263 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9218, some c9258, some c9260, some c9262, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9263 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9263 : lratChecker f9263 p9263 = .success := by decide +kernel
theorem unsat9263 : Unsatisfiable (PosFin 65) f9263 := by
  apply lratCheckerSound f9263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9263
  · intro a ha; simp [p9263] at ha; subst a; trivial
  · exact checked9263
theorem derived9263 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9263 := by
  apply localUnsat_implies_entails f9263 [c9218, c9258, c9260, c9262] c9263 unsat9263 (by rfl) a
  have h0 : Entails.eval a c9218 := derived9218 a h
  have h1 : Entails.eval a c9258 := derived9258 a h
  have h2 : Entails.eval a c9260 := derived9260 a h
  have h3 : Entails.eval a c9262 := derived9262 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9264 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9264 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3695, some c3696, some c3704, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p9264 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9264 : lratChecker f9264 p9264 = .success := by decide +kernel
theorem unsat9264 : Unsatisfiable (PosFin 65) f9264 := by
  apply lratCheckerSound f9264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9264
  · intro a ha; simp [p9264] at ha; subst a; trivial
  · exact checked9264
theorem derived9264 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9264 := by
  apply localUnsat_implies_entails f9264 [c3695, c3696, c3704] c9264 unsat9264 (by rfl) a
  have h0 : Entails.eval a c3695 := h 3694 (by decide)
  have h1 : Entails.eval a c3696 := h 3695 (by decide)
  have h2 : Entails.eval a c3704 := h 3703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9265 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9265 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9218, some c9263, some c9172, some c9193, some c3718, some c3732, some c8007, some c9178, some c9264, some c3703, some c3701, some c2982, some c2994, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9265 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9265 : lratChecker f9265 p9265 = .success := by decide +kernel
theorem unsat9265 : Unsatisfiable (PosFin 65) f9265 := by
  apply lratCheckerSound f9265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9265
  · intro a ha; simp [p9265] at ha; subst a; trivial
  · exact checked9265
theorem derived9265 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9265 := by
  apply localUnsat_implies_entails f9265 [c9218, c9263, c9172, c9193, c3718, c3732, c8007, c9178, c9264, c3703, c3701, c2982, c2994] c9265 unsat9265 (by rfl) a
  have h0 : Entails.eval a c9218 := derived9218 a h
  have h1 : Entails.eval a c9263 := derived9263 a h
  have h2 : Entails.eval a c9172 := derived9172 a h
  have h3 : Entails.eval a c9193 := derived9193 a h
  have h4 : Entails.eval a c3718 := h 3717 (by decide)
  have h5 : Entails.eval a c3732 := h 3731 (by decide)
  have h6 : Entails.eval a c8007 := derived8007 a h
  have h7 : Entails.eval a c9178 := derived9178 a h
  have h8 : Entails.eval a c9264 := derived9264 a h
  have h9 : Entails.eval a c3703 := h 3702 (by decide)
  have h10 : Entails.eval a c3701 := h 3700 (by decide)
  have h11 : Entails.eval a c2982 := h 2981 (by decide)
  have h12 : Entails.eval a c2994 := h 2993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9266 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9266 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2949, some c2612, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9266 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9266 : lratChecker f9266 p9266 = .success := by decide +kernel
theorem unsat9266 : Unsatisfiable (PosFin 65) f9266 := by
  apply lratCheckerSound f9266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9266
  · intro a ha; simp [p9266] at ha; subst a; trivial
  · exact checked9266
theorem derived9266 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9266 := by
  apply localUnsat_implies_entails f9266 [c2949, c2612] c9266 unsat9266 (by rfl) a
  have h0 : Entails.eval a c2949 := h 2948 (by decide)
  have h1 : Entails.eval a c2612 := h 2611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9267 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9267 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9178, some c8801, some c8837, some c593, some c2085, some c2084, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9267 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9267 : lratChecker f9267 p9267 = .success := by decide +kernel
theorem unsat9267 : Unsatisfiable (PosFin 65) f9267 := by
  apply lratCheckerSound f9267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9267
  · intro a ha; simp [p9267] at ha; subst a; trivial
  · exact checked9267
theorem derived9267 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9267 := by
  apply localUnsat_implies_entails f9267 [c9178, c8801, c8837, c593, c2085, c2084] c9267 unsat9267 (by rfl) a
  have h0 : Entails.eval a c9178 := derived9178 a h
  have h1 : Entails.eval a c8801 := derived8801 a h
  have h2 : Entails.eval a c8837 := derived8837 a h
  have h3 : Entails.eval a c593 := h 592 (by decide)
  have h4 : Entails.eval a c2085 := h 2084 (by decide)
  have h5 : Entails.eval a c2084 := h 2083 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9268 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨54, by decide⟩, false), (⟨29, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9268 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2934, some c738, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9268 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9268 : lratChecker f9268 p9268 = .success := by decide +kernel
theorem unsat9268 : Unsatisfiable (PosFin 65) f9268 := by
  apply lratCheckerSound f9268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9268
  · intro a ha; simp [p9268] at ha; subst a; trivial
  · exact checked9268
theorem derived9268 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9268 := by
  apply localUnsat_implies_entails f9268 [c2934, c738] c9268 unsat9268 (by rfl) a
  have h0 : Entails.eval a c2934 := h 2933 (by decide)
  have h1 : Entails.eval a c738 := h 737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9269 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9269 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9178, some c9193, some c9268, some c8801, some c9267, some c8837, some c3275, some c3280, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9269 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9269 : lratChecker f9269 p9269 = .success := by decide +kernel
theorem unsat9269 : Unsatisfiable (PosFin 65) f9269 := by
  apply lratCheckerSound f9269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9269
  · intro a ha; simp [p9269] at ha; subst a; trivial
  · exact checked9269
theorem derived9269 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9269 := by
  apply localUnsat_implies_entails f9269 [c9178, c9193, c9268, c8801, c9267, c8837, c3275, c3280] c9269 unsat9269 (by rfl) a
  have h0 : Entails.eval a c9178 := derived9178 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9268 := derived9268 a h
  have h3 : Entails.eval a c8801 := derived8801 a h
  have h4 : Entails.eval a c9267 := derived9267 a h
  have h5 : Entails.eval a c8837 := derived8837 a h
  have h6 : Entails.eval a c3275 := h 3274 (by decide)
  have h7 : Entails.eval a c3280 := h 3279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9270 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9270 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9265, some c9218, some c9263, some c9172, some c1090, some c9193, some c9147, some c9262, some c9259, some c1115, some c9266, some c1113, some c9267, some c8731, some c8386, some c3513, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9270 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9270 : lratChecker f9270 p9270 = .success := by decide +kernel
theorem unsat9270 : Unsatisfiable (PosFin 65) f9270 := by
  apply lratCheckerSound f9270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9270
  · intro a ha; simp [p9270] at ha; subst a; trivial
  · exact checked9270
theorem derived9270 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9270 := by
  apply localUnsat_implies_entails f9270 [c9265, c9218, c9263, c9172, c1090, c9193, c9147, c9262, c9259, c1115, c9266, c1113, c9267, c8731, c8386, c3513] c9270 unsat9270 (by rfl) a
  have h0 : Entails.eval a c9265 := derived9265 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9263 := derived9263 a h
  have h3 : Entails.eval a c9172 := derived9172 a h
  have h4 : Entails.eval a c1090 := h 1089 (by decide)
  have h5 : Entails.eval a c9193 := derived9193 a h
  have h6 : Entails.eval a c9147 := derived9147 a h
  have h7 : Entails.eval a c9262 := derived9262 a h
  have h8 : Entails.eval a c9259 := derived9259 a h
  have h9 : Entails.eval a c1115 := h 1114 (by decide)
  have h10 : Entails.eval a c9266 := derived9266 a h
  have h11 : Entails.eval a c1113 := h 1112 (by decide)
  have h12 : Entails.eval a c9267 := derived9267 a h
  have h13 : Entails.eval a c8731 := derived8731 a h
  have h14 : Entails.eval a c8386 := derived8386 a h
  have h15 : Entails.eval a c3513 := h 3512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9271 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9271 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9265, some c9218, some c9263, some c9172, some c1090, some c9193, some c9147, some c9262, some c9259, some c1115, some c9266, some c1113, some c1091, some c1108, some c9178, some c9269, some c9270, some c3270, some c3276, some c3271, some c3273, some c1067, some c1071, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9271 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9271 : lratChecker f9271 p9271 = .success := by decide +kernel
theorem unsat9271 : Unsatisfiable (PosFin 65) f9271 := by
  apply lratCheckerSound f9271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9271
  · intro a ha; simp [p9271] at ha; subst a; trivial
  · exact checked9271
theorem derived9271 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9271 := by
  apply localUnsat_implies_entails f9271 [c9265, c9218, c9263, c9172, c1090, c9193, c9147, c9262, c9259, c1115, c9266, c1113, c1091, c1108, c9178, c9269, c9270, c3270, c3276, c3271, c3273, c1067, c1071] c9271 unsat9271 (by rfl) a
  have h0 : Entails.eval a c9265 := derived9265 a h
  have h1 : Entails.eval a c9218 := derived9218 a h
  have h2 : Entails.eval a c9263 := derived9263 a h
  have h3 : Entails.eval a c9172 := derived9172 a h
  have h4 : Entails.eval a c1090 := h 1089 (by decide)
  have h5 : Entails.eval a c9193 := derived9193 a h
  have h6 : Entails.eval a c9147 := derived9147 a h
  have h7 : Entails.eval a c9262 := derived9262 a h
  have h8 : Entails.eval a c9259 := derived9259 a h
  have h9 : Entails.eval a c1115 := h 1114 (by decide)
  have h10 : Entails.eval a c9266 := derived9266 a h
  have h11 : Entails.eval a c1113 := h 1112 (by decide)
  have h12 : Entails.eval a c1091 := h 1090 (by decide)
  have h13 : Entails.eval a c1108 := h 1107 (by decide)
  have h14 : Entails.eval a c9178 := derived9178 a h
  have h15 : Entails.eval a c9269 := derived9269 a h
  have h16 : Entails.eval a c9270 := derived9270 a h
  have h17 : Entails.eval a c3270 := h 3269 (by decide)
  have h18 : Entails.eval a c3276 := h 3275 (by decide)
  have h19 : Entails.eval a c3271 := h 3270 (by decide)
  have h20 : Entails.eval a c3273 := h 3272 (by decide)
  have h21 : Entails.eval a c1067 := h 1066 (by decide)
  have h22 : Entails.eval a c1071 := h 1070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9272 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9272 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9218, some c9263, some c9172, some c9265, some c1090, some c1091, some c1108, some c9147, some c9178, some c9193, some c9267, some c9270, some c2934, some c738, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9272 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9272 : lratChecker f9272 p9272 = .success := by decide +kernel
theorem unsat9272 : Unsatisfiable (PosFin 65) f9272 := by
  apply lratCheckerSound f9272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9272
  · intro a ha; simp [p9272] at ha; subst a; trivial
  · exact checked9272
theorem derived9272 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9272 := by
  apply localUnsat_implies_entails f9272 [c9218, c9263, c9172, c9265, c1090, c1091, c1108, c9147, c9178, c9193, c9267, c9270, c2934, c738] c9272 unsat9272 (by rfl) a
  have h0 : Entails.eval a c9218 := derived9218 a h
  have h1 : Entails.eval a c9263 := derived9263 a h
  have h2 : Entails.eval a c9172 := derived9172 a h
  have h3 : Entails.eval a c9265 := derived9265 a h
  have h4 : Entails.eval a c1090 := h 1089 (by decide)
  have h5 : Entails.eval a c1091 := h 1090 (by decide)
  have h6 : Entails.eval a c1108 := h 1107 (by decide)
  have h7 : Entails.eval a c9147 := derived9147 a h
  have h8 : Entails.eval a c9178 := derived9178 a h
  have h9 : Entails.eval a c9193 := derived9193 a h
  have h10 : Entails.eval a c9267 := derived9267 a h
  have h11 : Entails.eval a c9270 := derived9270 a h
  have h12 : Entails.eval a c2934 := h 2933 (by decide)
  have h13 : Entails.eval a c738 := h 737 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9273 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9273 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9178, some c779, some c778, some c774, some c592, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9273 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9273 : lratChecker f9273 p9273 = .success := by decide +kernel
theorem unsat9273 : Unsatisfiable (PosFin 65) f9273 := by
  apply lratCheckerSound f9273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9273
  · intro a ha; simp [p9273] at ha; subst a; trivial
  · exact checked9273
theorem derived9273 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9273 := by
  apply localUnsat_implies_entails f9273 [c9178, c779, c778, c774, c592] c9273 unsat9273 (by rfl) a
  have h0 : Entails.eval a c9178 := derived9178 a h
  have h1 : Entails.eval a c779 := h 778 (by decide)
  have h2 : Entails.eval a c778 := h 777 (by decide)
  have h3 : Entails.eval a c774 := h 773 (by decide)
  have h4 : Entails.eval a c592 := h 591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9274 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9274 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9273, some c9178, some c9193, some c8801, some c8835, some c8837, some c593, some c8846, some c590, some c589, some c1071, some c1065, some c1064, some c191, some c1086, some c1087, some c1085, some c119, some c2806, some c3372, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9274 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9274 : lratChecker f9274 p9274 = .success := by decide +kernel
theorem unsat9274 : Unsatisfiable (PosFin 65) f9274 := by
  apply lratCheckerSound f9274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9274
  · intro a ha; simp [p9274] at ha; subst a; trivial
  · exact checked9274
theorem derived9274 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9274 := by
  apply localUnsat_implies_entails f9274 [c9273, c9178, c9193, c8801, c8835, c8837, c593, c8846, c590, c589, c1071, c1065, c1064, c191, c1086, c1087, c1085, c119, c2806, c3372] c9274 unsat9274 (by rfl) a
  have h0 : Entails.eval a c9273 := derived9273 a h
  have h1 : Entails.eval a c9178 := derived9178 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c8801 := derived8801 a h
  have h4 : Entails.eval a c8835 := derived8835 a h
  have h5 : Entails.eval a c8837 := derived8837 a h
  have h6 : Entails.eval a c593 := h 592 (by decide)
  have h7 : Entails.eval a c8846 := derived8846 a h
  have h8 : Entails.eval a c590 := h 589 (by decide)
  have h9 : Entails.eval a c589 := h 588 (by decide)
  have h10 : Entails.eval a c1071 := h 1070 (by decide)
  have h11 : Entails.eval a c1065 := h 1064 (by decide)
  have h12 : Entails.eval a c1064 := h 1063 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c1086 := h 1085 (by decide)
  have h15 : Entails.eval a c1087 := h 1086 (by decide)
  have h16 : Entails.eval a c1085 := h 1084 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c2806 := h 2805 (by decide)
  have h19 : Entails.eval a c3372 := h 3371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9275 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9275 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9218, some c9263, some c9172, some c9265, some c9262, some c9147, some c1091, some c1090, some c9259, some c1108, some c1115, some c9271, some c9272, some c9273, some c9274, some c8731, some c2605, some c3513, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9275 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9275 : lratChecker f9275 p9275 = .success := by decide +kernel
theorem unsat9275 : Unsatisfiable (PosFin 65) f9275 := by
  apply lratCheckerSound f9275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9275
  · intro a ha; simp [p9275] at ha; subst a; trivial
  · exact checked9275
theorem derived9275 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9275 := by
  apply localUnsat_implies_entails f9275 [c9218, c9263, c9172, c9265, c9262, c9147, c1091, c1090, c9259, c1108, c1115, c9271, c9272, c9273, c9274, c8731, c2605, c3513] c9275 unsat9275 (by rfl) a
  have h0 : Entails.eval a c9218 := derived9218 a h
  have h1 : Entails.eval a c9263 := derived9263 a h
  have h2 : Entails.eval a c9172 := derived9172 a h
  have h3 : Entails.eval a c9265 := derived9265 a h
  have h4 : Entails.eval a c9262 := derived9262 a h
  have h5 : Entails.eval a c9147 := derived9147 a h
  have h6 : Entails.eval a c1091 := h 1090 (by decide)
  have h7 : Entails.eval a c1090 := h 1089 (by decide)
  have h8 : Entails.eval a c9259 := derived9259 a h
  have h9 : Entails.eval a c1108 := h 1107 (by decide)
  have h10 : Entails.eval a c1115 := h 1114 (by decide)
  have h11 : Entails.eval a c9271 := derived9271 a h
  have h12 : Entails.eval a c9272 := derived9272 a h
  have h13 : Entails.eval a c9273 := derived9273 a h
  have h14 : Entails.eval a c9274 := derived9274 a h
  have h15 : Entails.eval a c8731 := derived8731 a h
  have h16 : Entails.eval a c2605 := h 2604 (by decide)
  have h17 : Entails.eval a c3513 := h 3512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9276 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨63, by decide⟩, true), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9276 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3250, some c3257, some c3235, some c3252, some c3256, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9276 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9276 : lratChecker f9276 p9276 = .success := by decide +kernel
theorem unsat9276 : Unsatisfiable (PosFin 65) f9276 := by
  apply lratCheckerSound f9276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9276
  · intro a ha; simp [p9276] at ha; subst a; trivial
  · exact checked9276
theorem derived9276 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9276 := by
  apply localUnsat_implies_entails f9276 [c3250, c3257, c3235, c3252, c3256] c9276 unsat9276 (by rfl) a
  have h0 : Entails.eval a c3250 := h 3249 (by decide)
  have h1 : Entails.eval a c3257 := h 3256 (by decide)
  have h2 : Entails.eval a c3235 := h 3234 (by decide)
  have h3 : Entails.eval a c3252 := h 3251 (by decide)
  have h4 : Entails.eval a c3256 := h 3255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9277 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨63, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9277 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3347, some c3657, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9277 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9277 : lratChecker f9277 p9277 = .success := by decide +kernel
theorem unsat9277 : Unsatisfiable (PosFin 65) f9277 := by
  apply lratCheckerSound f9277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9277
  · intro a ha; simp [p9277] at ha; subst a; trivial
  · exact checked9277
theorem derived9277 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9277 := by
  apply localUnsat_implies_entails f9277 [c3347, c3657] c9277 unsat9277 (by rfl) a
  have h0 : Entails.eval a c3347 := h 3346 (by decide)
  have h1 : Entails.eval a c3657 := h 3656 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9278 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨64, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9278 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c9276, some c9277, some c9219, some c3343, some c2786, some c3645, some c3631, some c4258, some c4043, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9278 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9278 : lratChecker f9278 p9278 = .success := by decide +kernel
theorem unsat9278 : Unsatisfiable (PosFin 65) f9278 := by
  apply lratCheckerSound f9278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9278
  · intro a ha; simp [p9278] at ha; subst a; trivial
  · exact checked9278
theorem derived9278 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9278 := by
  apply localUnsat_implies_entails f9278 [c8269, c7994, c9276, c9277, c9219, c3343, c2786, c3645, c3631, c4258, c4043] c9278 unsat9278 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c9276 := derived9276 a h
  have h3 : Entails.eval a c9277 := derived9277 a h
  have h4 : Entails.eval a c9219 := derived9219 a h
  have h5 : Entails.eval a c3343 := h 3342 (by decide)
  have h6 : Entails.eval a c2786 := h 2785 (by decide)
  have h7 : Entails.eval a c3645 := h 3644 (by decide)
  have h8 : Entails.eval a c3631 := h 3630 (by decide)
  have h9 : Entails.eval a c4258 := h 4257 (by decide)
  have h10 : Entails.eval a c4043 := h 4042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9279 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨60, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨64, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9279 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8300, some c8380, some c3266, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9279 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9279 : lratChecker f9279 p9279 = .success := by decide +kernel
theorem unsat9279 : Unsatisfiable (PosFin 65) f9279 := by
  apply lratCheckerSound f9279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9279
  · intro a ha; simp [p9279] at ha; subst a; trivial
  · exact checked9279
theorem derived9279 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9279 := by
  apply localUnsat_implies_entails f9279 [c8300, c8380, c3266] c9279 unsat9279 (by rfl) a
  have h0 : Entails.eval a c8300 := derived8300 a h
  have h1 : Entails.eval a c8380 := derived8380 a h
  have h2 : Entails.eval a c3266 := h 3265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9280 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨64, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9280 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c3235, some c9279, some c3254, some c9249, some c3251, some c3267, some c9254, some c3255, some c3266, some c9221, some c3795, some c1391, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9280 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9280 : lratChecker f9280 p9280 = .success := by decide +kernel
theorem unsat9280 : Unsatisfiable (PosFin 65) f9280 := by
  apply lratCheckerSound f9280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9280
  · intro a ha; simp [p9280] at ha; subst a; trivial
  · exact checked9280
theorem derived9280 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9280 := by
  apply localUnsat_implies_entails f9280 [c8269, c7994, c3235, c9279, c3254, c9249, c3251, c3267, c9254, c3255, c3266, c9221, c3795, c1391] c9280 unsat9280 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c3235 := h 3234 (by decide)
  have h3 : Entails.eval a c9279 := derived9279 a h
  have h4 : Entails.eval a c3254 := h 3253 (by decide)
  have h5 : Entails.eval a c9249 := derived9249 a h
  have h6 : Entails.eval a c3251 := h 3250 (by decide)
  have h7 : Entails.eval a c3267 := h 3266 (by decide)
  have h8 : Entails.eval a c9254 := derived9254 a h
  have h9 : Entails.eval a c3255 := h 3254 (by decide)
  have h10 : Entails.eval a c3266 := h 3265 (by decide)
  have h11 : Entails.eval a c9221 := derived9221 a h
  have h12 : Entails.eval a c3795 := h 3794 (by decide)
  have h13 : Entails.eval a c1391 := h 1390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9281 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9275, some c9278, some c9280, some c8269, some c9178, some c8300, some c8380, some c9219, some c9195, some c8580, some c9252, some c3631, some c3666, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9281 : lratChecker f9281 p9281 = .success := by decide +kernel
theorem unsat9281 : Unsatisfiable (PosFin 65) f9281 := by
  apply lratCheckerSound f9281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9281
  · intro a ha; simp [p9281] at ha; subst a; trivial
  · exact checked9281
theorem derived9281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9281 := by
  apply localUnsat_implies_entails f9281 [c9193, c9275, c9278, c9280, c8269, c9178, c8300, c8380, c9219, c9195, c8580, c9252, c3631, c3666] c9281 unsat9281 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9275 := derived9275 a h
  have h2 : Entails.eval a c9278 := derived9278 a h
  have h3 : Entails.eval a c9280 := derived9280 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c9178 := derived9178 a h
  have h6 : Entails.eval a c8300 := derived8300 a h
  have h7 : Entails.eval a c8380 := derived8380 a h
  have h8 : Entails.eval a c9219 := derived9219 a h
  have h9 : Entails.eval a c9195 := derived9195 a h
  have h10 : Entails.eval a c8580 := derived8580 a h
  have h11 : Entails.eval a c9252 := derived9252 a h
  have h12 : Entails.eval a c3631 := h 3630 (by decide)
  have h13 : Entails.eval a c3666 := h 3665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9282 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨52, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c3645, some c3631, some c2787, some c4043, some c4258, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9282 : lratChecker f9282 p9282 = .success := by decide +kernel
theorem unsat9282 : Unsatisfiable (PosFin 65) f9282 := by
  apply lratCheckerSound f9282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9282
  · intro a ha; simp [p9282] at ha; subst a; trivial
  · exact checked9282
theorem derived9282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9282 := by
  apply localUnsat_implies_entails f9282 [c8269, c7994, c3645, c3631, c2787, c4043, c4258] c9282 unsat9282 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c3645 := h 3644 (by decide)
  have h3 : Entails.eval a c3631 := h 3630 (by decide)
  have h4 : Entails.eval a c2787 := h 2786 (by decide)
  have h5 : Entails.eval a c4043 := h 4042 (by decide)
  have h6 : Entails.eval a c4258 := h 4257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9283 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9275, some c8269, some c7994, some c9193, some c9278, some c9280, some c9281, some c9282, some c3341, some c9248, some c3357, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9283 : lratChecker f9283 p9283 = .success := by decide +kernel
theorem unsat9283 : Unsatisfiable (PosFin 65) f9283 := by
  apply lratCheckerSound f9283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9283
  · intro a ha; simp [p9283] at ha; subst a; trivial
  · exact checked9283
theorem derived9283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9283 := by
  apply localUnsat_implies_entails f9283 [c9275, c8269, c7994, c9193, c9278, c9280, c9281, c9282, c3341, c9248, c3357] c9283 unsat9283 (by rfl) a
  have h0 : Entails.eval a c9275 := derived9275 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c9193 := derived9193 a h
  have h4 : Entails.eval a c9278 := derived9278 a h
  have h5 : Entails.eval a c9280 := derived9280 a h
  have h6 : Entails.eval a c9281 := derived9281 a h
  have h7 : Entails.eval a c9282 := derived9282 a h
  have h8 : Entails.eval a c3341 := h 3340 (by decide)
  have h9 : Entails.eval a c9248 := derived9248 a h
  have h10 : Entails.eval a c3357 := h 3356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9284 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨64, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c3748, some c8269, some c9175, some c3743, some c3741, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p9284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9284 : lratChecker f9284 p9284 = .success := by decide +kernel
theorem unsat9284 : Unsatisfiable (PosFin 65) f9284 := by
  apply lratCheckerSound f9284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9284
  · intro a ha; simp [p9284] at ha; subst a; trivial
  · exact checked9284
theorem derived9284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9284 := by
  apply localUnsat_implies_entails f9284 [c7994, c3748, c8269, c9175, c3743, c3741] c9284 unsat9284 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c3748 := h 3747 (by decide)
  have h2 : Entails.eval a c8269 := derived8269 a h
  have h3 : Entails.eval a c9175 := derived9175 a h
  have h4 : Entails.eval a c3743 := h 3742 (by decide)
  have h5 : Entails.eval a c3741 := h 3740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9285 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨54, by decide⟩, false), (⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨64, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c3459, some c3449, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9285 : lratChecker f9285 p9285 = .success := by decide +kernel
theorem unsat9285 : Unsatisfiable (PosFin 65) f9285 := by
  apply lratCheckerSound f9285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9285
  · intro a ha; simp [p9285] at ha; subst a; trivial
  · exact checked9285
theorem derived9285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9285 := by
  apply localUnsat_implies_entails f9285 [c8269, c7994, c3459, c3449] c9285 unsat9285 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c3459 := h 3458 (by decide)
  have h3 : Entails.eval a c3449 := h 3448 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9286 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨59, by decide⟩, false), (⟨58, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3695, some c2969, some c3697, some c2987, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9286 : lratChecker f9286 p9286 = .success := by decide +kernel
theorem unsat9286 : Unsatisfiable (PosFin 65) f9286 := by
  apply lratCheckerSound f9286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9286
  · intro a ha; simp [p9286] at ha; subst a; trivial
  · exact checked9286
theorem derived9286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9286 := by
  apply localUnsat_implies_entails f9286 [c3695, c2969, c3697, c2987] c9286 unsat9286 (by rfl) a
  have h0 : Entails.eval a c3695 := h 3694 (by decide)
  have h1 : Entails.eval a c2969 := h 2968 (by decide)
  have h2 : Entails.eval a c3697 := h 3696 (by decide)
  have h3 : Entails.eval a c2987 := h 2986 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9287 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9275, some c8269, some c9178, some c7994, some c9193, some c9283, some c3009, some c3748, some c9284, some c9286, some c3703, some c3701, some c8801, some c8837, some c3711, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9287 : lratChecker f9287 p9287 = .success := by decide +kernel
theorem unsat9287 : Unsatisfiable (PosFin 65) f9287 := by
  apply lratCheckerSound f9287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9287
  · intro a ha; simp [p9287] at ha; subst a; trivial
  · exact checked9287
theorem derived9287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9287 := by
  apply localUnsat_implies_entails f9287 [c9275, c8269, c9178, c7994, c9193, c9283, c3009, c3748, c9284, c9286, c3703, c3701, c8801, c8837, c3711] c9287 unsat9287 (by rfl) a
  have h0 : Entails.eval a c9275 := derived9275 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9178 := derived9178 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9193 := derived9193 a h
  have h5 : Entails.eval a c9283 := derived9283 a h
  have h6 : Entails.eval a c3009 := h 3008 (by decide)
  have h7 : Entails.eval a c3748 := h 3747 (by decide)
  have h8 : Entails.eval a c9284 := derived9284 a h
  have h9 : Entails.eval a c9286 := derived9286 a h
  have h10 : Entails.eval a c3703 := h 3702 (by decide)
  have h11 : Entails.eval a c3701 := h 3700 (by decide)
  have h12 : Entails.eval a c8801 := derived8801 a h
  have h13 : Entails.eval a c8837 := derived8837 a h
  have h14 : Entails.eval a c3711 := h 3710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9288 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9287, some c9275, some c7994, some c9193, some c9259, some c1097, some c1101, some c1091, some c1103, some c1114, some c1118, some c1089, some c1111, some c8419, some c1102, some c9221, some c9246, some c9282, some c9285, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9288 : lratChecker f9288 p9288 = .success := by decide +kernel
theorem unsat9288 : Unsatisfiable (PosFin 65) f9288 := by
  apply lratCheckerSound f9288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9288
  · intro a ha; simp [p9288] at ha; subst a; trivial
  · exact checked9288
theorem derived9288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9288 := by
  apply localUnsat_implies_entails f9288 [c9287, c9275, c7994, c9193, c9259, c1097, c1101, c1091, c1103, c1114, c1118, c1089, c1111, c8419, c1102, c9221, c9246, c9282, c9285] c9288 unsat9288 (by rfl) a
  have h0 : Entails.eval a c9287 := derived9287 a h
  have h1 : Entails.eval a c9275 := derived9275 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c9193 := derived9193 a h
  have h4 : Entails.eval a c9259 := derived9259 a h
  have h5 : Entails.eval a c1097 := h 1096 (by decide)
  have h6 : Entails.eval a c1101 := h 1100 (by decide)
  have h7 : Entails.eval a c1091 := h 1090 (by decide)
  have h8 : Entails.eval a c1103 := h 1102 (by decide)
  have h9 : Entails.eval a c1114 := h 1113 (by decide)
  have h10 : Entails.eval a c1118 := h 1117 (by decide)
  have h11 : Entails.eval a c1089 := h 1088 (by decide)
  have h12 : Entails.eval a c1111 := h 1110 (by decide)
  have h13 : Entails.eval a c8419 := derived8419 a h
  have h14 : Entails.eval a c1102 := h 1101 (by decide)
  have h15 : Entails.eval a c9221 := derived9221 a h
  have h16 : Entails.eval a c9246 := derived9246 a h
  have h17 : Entails.eval a c9282 := derived9282 a h
  have h18 : Entails.eval a c9285 := derived9285 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9289 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨9, by decide⟩, false), (⟨64, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7994, some c1104, some c1116, some c1103, some c1100, some c1101, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9289 : lratChecker f9289 p9289 = .success := by decide +kernel
theorem unsat9289 : Unsatisfiable (PosFin 65) f9289 := by
  apply lratCheckerSound f9289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9289
  · intro a ha; simp [p9289] at ha; subst a; trivial
  · exact checked9289
theorem derived9289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9289 := by
  apply localUnsat_implies_entails f9289 [c7994, c1104, c1116, c1103, c1100, c1101] c9289 unsat9289 (by rfl) a
  have h0 : Entails.eval a c7994 := derived7994 a h
  have h1 : Entails.eval a c1104 := h 1103 (by decide)
  have h2 : Entails.eval a c1116 := h 1115 (by decide)
  have h3 : Entails.eval a c1103 := h 1102 (by decide)
  have h4 : Entails.eval a c1100 := h 1099 (by decide)
  have h5 : Entails.eval a c1101 := h 1100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9290 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c721, some c8624, some c122, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9290 : lratChecker f9290 p9290 = .success := by decide +kernel
theorem unsat9290 : Unsatisfiable (PosFin 65) f9290 := by
  apply lratCheckerSound f9290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9290
  · intro a ha; simp [p9290] at ha; subst a; trivial
  · exact checked9290
theorem derived9290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9290 := by
  apply localUnsat_implies_entails f9290 [c721, c8624, c122] c9290 unsat9290 (by rfl) a
  have h0 : Entails.eval a c721 := h 720 (by decide)
  have h1 : Entails.eval a c8624 := derived8624 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9291 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨32, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨9, by decide⟩, false), (⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1091, some c1089, some c9290, some c2087, some c2079, some c1078, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9291 : lratChecker f9291 p9291 = .success := by decide +kernel
theorem unsat9291 : Unsatisfiable (PosFin 65) f9291 := by
  apply lratCheckerSound f9291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9291
  · intro a ha; simp [p9291] at ha; subst a; trivial
  · exact checked9291
theorem derived9291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9291 := by
  apply localUnsat_implies_entails f9291 [c1091, c1089, c9290, c2087, c2079, c1078] c9291 unsat9291 (by rfl) a
  have h0 : Entails.eval a c1091 := h 1090 (by decide)
  have h1 : Entails.eval a c1089 := h 1088 (by decide)
  have h2 : Entails.eval a c9290 := derived9290 a h
  have h3 : Entails.eval a c2087 := h 2086 (by decide)
  have h4 : Entails.eval a c2079 := h 2078 (by decide)
  have h5 : Entails.eval a c1078 := h 1077 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9292 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9275, some c7994, some c8269, some c9178, some c9287, some c9289, some c9259, some c9288, some c1097, some c1101, some c1091, some c1103, some c1114, some c1118, some c1089, some c9181, some c1111, some c9119, some c8731, some c9268, some c8846, some c9291, some c9221, some c9246, some c3384, some c3377, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked9292 : lratChecker f9292 p9292 = .success := by decide +kernel
theorem unsat9292 : Unsatisfiable (PosFin 65) f9292 := by
  apply lratCheckerSound f9292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9292
  · intro a ha; simp [p9292] at ha; subst a; trivial
  · exact checked9292
theorem derived9292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9292 := by
  apply localUnsat_implies_entails f9292 [c9193, c9275, c7994, c8269, c9178, c9287, c9289, c9259, c9288, c1097, c1101, c1091, c1103, c1114, c1118, c1089, c9181, c1111, c9119, c8731, c9268, c8846, c9291, c9221, c9246, c3384, c3377] c9292 unsat9292 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9275 := derived9275 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c9178 := derived9178 a h
  have h5 : Entails.eval a c9287 := derived9287 a h
  have h6 : Entails.eval a c9289 := derived9289 a h
  have h7 : Entails.eval a c9259 := derived9259 a h
  have h8 : Entails.eval a c9288 := derived9288 a h
  have h9 : Entails.eval a c1097 := h 1096 (by decide)
  have h10 : Entails.eval a c1101 := h 1100 (by decide)
  have h11 : Entails.eval a c1091 := h 1090 (by decide)
  have h12 : Entails.eval a c1103 := h 1102 (by decide)
  have h13 : Entails.eval a c1114 := h 1113 (by decide)
  have h14 : Entails.eval a c1118 := h 1117 (by decide)
  have h15 : Entails.eval a c1089 := h 1088 (by decide)
  have h16 : Entails.eval a c9181 := derived9181 a h
  have h17 : Entails.eval a c1111 := h 1110 (by decide)
  have h18 : Entails.eval a c9119 := derived9119 a h
  have h19 : Entails.eval a c8731 := derived8731 a h
  have h20 : Entails.eval a c9268 := derived9268 a h
  have h21 : Entails.eval a c8846 := derived8846 a h
  have h22 : Entails.eval a c9291 := derived9291 a h
  have h23 : Entails.eval a c9221 := derived9221 a h
  have h24 : Entails.eval a c9246 := derived9246 a h
  have h25 : Entails.eval a c3384 := h 3383 (by decide)
  have h26 : Entails.eval a c3377 := h 3376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9293 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3239, some c3330, some c3635, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9293 : lratChecker f9293 p9293 = .success := by decide +kernel
theorem unsat9293 : Unsatisfiable (PosFin 65) f9293 := by
  apply lratCheckerSound f9293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9293
  · intro a ha; simp [p9293] at ha; subst a; trivial
  · exact checked9293
theorem derived9293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9293 := by
  apply localUnsat_implies_entails f9293 [c3239, c3330, c3635] c9293 unsat9293 (by rfl) a
  have h0 : Entails.eval a c3239 := h 3238 (by decide)
  have h1 : Entails.eval a c3330 := h 3329 (by decide)
  have h2 : Entails.eval a c3635 := h 3634 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9294 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3240, some c3243, some c3255, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9294 : lratChecker f9294 p9294 = .success := by decide +kernel
theorem unsat9294 : Unsatisfiable (PosFin 65) f9294 := by
  apply lratCheckerSound f9294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9294
  · intro a ha; simp [p9294] at ha; subst a; trivial
  · exact checked9294
theorem derived9294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9294 := by
  apply localUnsat_implies_entails f9294 [c3240, c3243, c3255] c9294 unsat9294 (by rfl) a
  have h0 : Entails.eval a c3240 := h 3239 (by decide)
  have h1 : Entails.eval a c3243 := h 3242 (by decide)
  have h2 : Entails.eval a c3255 := h 3254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9295 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨63, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3333, some c3346, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9295 : lratChecker f9295 p9295 = .success := by decide +kernel
theorem unsat9295 : Unsatisfiable (PosFin 65) f9295 := by
  apply lratCheckerSound f9295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9295
  · intro a ha; simp [p9295] at ha; subst a; trivial
  · exact checked9295
theorem derived9295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9295 := by
  apply localUnsat_implies_entails f9295 [c3333, c3346] c9295 unsat9295 (by rfl) a
  have h0 : Entails.eval a c3333 := h 3332 (by decide)
  have h1 : Entails.eval a c3346 := h 3345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9296 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨55, by decide⟩, true), (⟨62, by decide⟩, false), (⟨58, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3668, some c3670, some c3664, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9296 : lratChecker f9296 p9296 = .success := by decide +kernel
theorem unsat9296 : Unsatisfiable (PosFin 65) f9296 := by
  apply lratCheckerSound f9296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9296
  · intro a ha; simp [p9296] at ha; subst a; trivial
  · exact checked9296
theorem derived9296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9296 := by
  apply localUnsat_implies_entails f9296 [c3668, c3670, c3664] c9296 unsat9296 (by rfl) a
  have h0 : Entails.eval a c3668 := h 3667 (by decide)
  have h1 : Entails.eval a c3670 := h 3669 (by decide)
  have h2 : Entails.eval a c3664 := h 3663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9297 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9245, some c3374, some c3683, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9297 : lratChecker f9297 p9297 = .success := by decide +kernel
theorem unsat9297 : Unsatisfiable (PosFin 65) f9297 := by
  apply lratCheckerSound f9297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9297
  · intro a ha; simp [p9297] at ha; subst a; trivial
  · exact checked9297
theorem derived9297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9297 := by
  apply localUnsat_implies_entails f9297 [c9245, c3374, c3683] c9297 unsat9297 (by rfl) a
  have h0 : Entails.eval a c9245 := derived9245 a h
  have h1 : Entails.eval a c3374 := h 3373 (by decide)
  have h2 : Entails.eval a c3683 := h 3682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9298 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9293, some c9294, some c3331, some c3350, some c3332, some c9297, some c1364, some c1380, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9298 : lratChecker f9298 p9298 = .success := by decide +kernel
theorem unsat9298 : Unsatisfiable (PosFin 65) f9298 := by
  apply lratCheckerSound f9298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9298
  · intro a ha; simp [p9298] at ha; subst a; trivial
  · exact checked9298
theorem derived9298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9298 := by
  apply localUnsat_implies_entails f9298 [c9193, c9293, c9294, c3331, c3350, c3332, c9297, c1364, c1380] c9298 unsat9298 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9294 := derived9294 a h
  have h3 : Entails.eval a c3331 := h 3330 (by decide)
  have h4 : Entails.eval a c3350 := h 3349 (by decide)
  have h5 : Entails.eval a c3332 := h 3331 (by decide)
  have h6 : Entails.eval a c9297 := derived9297 a h
  have h7 : Entails.eval a c1364 := h 1363 (by decide)
  have h8 : Entails.eval a c1380 := h 1379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9299 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨13, by decide⟩, false), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c3654, some c3660, some c8409, some c9297, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9299 : lratChecker f9299 p9299 = .success := by decide +kernel
theorem unsat9299 : Unsatisfiable (PosFin 65) f9299 := by
  apply lratCheckerSound f9299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9299
  · intro a ha; simp [p9299] at ha; subst a; trivial
  · exact checked9299
theorem derived9299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9299 := by
  apply localUnsat_implies_entails f9299 [c9193, c3654, c3660, c8409, c9297] c9299 unsat9299 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c3654 := h 3653 (by decide)
  have h2 : Entails.eval a c3660 := h 3659 (by decide)
  have h3 : Entails.eval a c8409 := derived8409 a h
  have h4 : Entails.eval a c9297 := derived9297 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9300 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9293, some c9294, some c9298, some c9299, some c3636, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9300 : lratChecker f9300 p9300 = .success := by decide +kernel
theorem unsat9300 : Unsatisfiable (PosFin 65) f9300 := by
  apply lratCheckerSound f9300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9300
  · intro a ha; simp [p9300] at ha; subst a; trivial
  · exact checked9300
theorem derived9300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9300 := by
  apply localUnsat_implies_entails f9300 [c9193, c9293, c9294, c9298, c9299, c3636] c9300 unsat9300 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9294 := derived9294 a h
  have h3 : Entails.eval a c9298 := derived9298 a h
  have h4 : Entails.eval a c9299 := derived9299 a h
  have h5 : Entails.eval a c3636 := h 3635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9301 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨54, by decide⟩, false), (⟨13, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9254, some c3346, some c3351, some c3332, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9301 : lratChecker f9301 p9301 = .success := by decide +kernel
theorem unsat9301 : Unsatisfiable (PosFin 65) f9301 := by
  apply lratCheckerSound f9301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9301
  · intro a ha; simp [p9301] at ha; subst a; trivial
  · exact checked9301
theorem derived9301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9301 := by
  apply localUnsat_implies_entails f9301 [c9254, c3346, c3351, c3332] c9301 unsat9301 (by rfl) a
  have h0 : Entails.eval a c9254 := derived9254 a h
  have h1 : Entails.eval a c3346 := h 3345 (by decide)
  have h2 : Entails.eval a c3351 := h 3350 (by decide)
  have h3 : Entails.eval a c3332 := h 3331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9302 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9300, some c9193, some c9293, some c9294, some c3331, some c9301, some c3335, some c3351, some c9297, some c3332, some c1364, some c1380, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9302 : lratChecker f9302 p9302 = .success := by decide +kernel
theorem unsat9302 : Unsatisfiable (PosFin 65) f9302 := by
  apply lratCheckerSound f9302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9302
  · intro a ha; simp [p9302] at ha; subst a; trivial
  · exact checked9302
theorem derived9302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9302 := by
  apply localUnsat_implies_entails f9302 [c9300, c9193, c9293, c9294, c3331, c9301, c3335, c3351, c9297, c3332, c1364, c1380] c9302 unsat9302 (by rfl) a
  have h0 : Entails.eval a c9300 := derived9300 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9293 := derived9293 a h
  have h3 : Entails.eval a c9294 := derived9294 a h
  have h4 : Entails.eval a c3331 := h 3330 (by decide)
  have h5 : Entails.eval a c9301 := derived9301 a h
  have h6 : Entails.eval a c3335 := h 3334 (by decide)
  have h7 : Entails.eval a c3351 := h 3350 (by decide)
  have h8 : Entails.eval a c9297 := derived9297 a h
  have h9 : Entails.eval a c3332 := h 3331 (by decide)
  have h10 : Entails.eval a c1364 := h 1363 (by decide)
  have h11 : Entails.eval a c1380 := h 1379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9303 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9293, some c9294, some c9300, some c9302, some c3653, some c3646, some c3648, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9303 : lratChecker f9303 p9303 = .success := by decide +kernel
theorem unsat9303 : Unsatisfiable (PosFin 65) f9303 := by
  apply lratCheckerSound f9303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9303
  · intro a ha; simp [p9303] at ha; subst a; trivial
  · exact checked9303
theorem derived9303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9303 := by
  apply localUnsat_implies_entails f9303 [c9193, c9293, c9294, c9300, c9302, c3653, c3646, c3648] c9303 unsat9303 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9294 := derived9294 a h
  have h3 : Entails.eval a c9300 := derived9300 a h
  have h4 : Entails.eval a c9302 := derived9302 a h
  have h5 : Entails.eval a c3653 := h 3652 (by decide)
  have h6 : Entails.eval a c3646 := h 3645 (by decide)
  have h7 : Entails.eval a c3648 := h 3647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9304 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9295, some c3335, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9304 : lratChecker f9304 p9304 = .success := by decide +kernel
theorem unsat9304 : Unsatisfiable (PosFin 65) f9304 := by
  apply lratCheckerSound f9304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9304
  · intro a ha; simp [p9304] at ha; subst a; trivial
  · exact checked9304
theorem derived9304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9304 := by
  apply localUnsat_implies_entails f9304 [c9295, c3335] c9304 unsat9304 (by rfl) a
  have h0 : Entails.eval a c9295 := derived9295 a h
  have h1 : Entails.eval a c3335 := h 3334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9305 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3331, some c3339, some c9304, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9305 : lratChecker f9305 p9305 = .success := by decide +kernel
theorem unsat9305 : Unsatisfiable (PosFin 65) f9305 := by
  apply lratCheckerSound f9305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9305
  · intro a ha; simp [p9305] at ha; subst a; trivial
  · exact checked9305
theorem derived9305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9305 := by
  apply localUnsat_implies_entails f9305 [c3331, c3339, c9304] c9305 unsat9305 (by rfl) a
  have h0 : Entails.eval a c3331 := h 3330 (by decide)
  have h1 : Entails.eval a c3339 := h 3338 (by decide)
  have h2 : Entails.eval a c9304 := derived9304 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9306 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨62, by decide⟩, false), (⟨54, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3660, some c9296, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9306 : lratChecker f9306 p9306 = .success := by decide +kernel
theorem unsat9306 : Unsatisfiable (PosFin 65) f9306 := by
  apply lratCheckerSound f9306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9306
  · intro a ha; simp [p9306] at ha; subst a; trivial
  · exact checked9306
theorem derived9306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9306 := by
  apply localUnsat_implies_entails f9306 [c3660, c9296] c9306 unsat9306 (by rfl) a
  have h0 : Entails.eval a c3660 := h 3659 (by decide)
  have h1 : Entails.eval a c9296 := derived9296 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9307 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9293, some c9294, some c9303, some c9305, some c3636, some c3644, some c3640, some c9306, some c3653, some c3649, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9307 : lratChecker f9307 p9307 = .success := by decide +kernel
theorem unsat9307 : Unsatisfiable (PosFin 65) f9307 := by
  apply lratCheckerSound f9307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9307
  · intro a ha; simp [p9307] at ha; subst a; trivial
  · exact checked9307
theorem derived9307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9307 := by
  apply localUnsat_implies_entails f9307 [c9193, c9293, c9294, c9303, c9305, c3636, c3644, c3640, c9306, c3653, c3649] c9307 unsat9307 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9293 := derived9293 a h
  have h2 : Entails.eval a c9294 := derived9294 a h
  have h3 : Entails.eval a c9303 := derived9303 a h
  have h4 : Entails.eval a c9305 := derived9305 a h
  have h5 : Entails.eval a c3636 := h 3635 (by decide)
  have h6 : Entails.eval a c3644 := h 3643 (by decide)
  have h7 : Entails.eval a c3640 := h 3639 (by decide)
  have h8 : Entails.eval a c9306 := derived9306 a h
  have h9 : Entails.eval a c3653 := h 3652 (by decide)
  have h10 : Entails.eval a c3649 := h 3648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9308 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9292, some c9193, some c9307, some c9185, some c3005, some c3002, some c3013, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9308 : lratChecker f9308 p9308 = .success := by decide +kernel
theorem unsat9308 : Unsatisfiable (PosFin 65) f9308 := by
  apply lratCheckerSound f9308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9308
  · intro a ha; simp [p9308] at ha; subst a; trivial
  · exact checked9308
theorem derived9308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9308 := by
  apply localUnsat_implies_entails f9308 [c9292, c9193, c9307, c9185, c3005, c3002, c3013] c9308 unsat9308 (by rfl) a
  have h0 : Entails.eval a c9292 := derived9292 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9307 := derived9307 a h
  have h3 : Entails.eval a c9185 := derived9185 a h
  have h4 : Entails.eval a c3005 := h 3004 (by decide)
  have h5 : Entails.eval a c3002 := h 3001 (by decide)
  have h6 : Entails.eval a c3013 := h 3012 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9309 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨63, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3238, some c3329, some c3634, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9309 : lratChecker f9309 p9309 = .success := by decide +kernel
theorem unsat9309 : Unsatisfiable (PosFin 65) f9309 := by
  apply lratCheckerSound f9309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9309
  · intro a ha; simp [p9309] at ha; subst a; trivial
  · exact checked9309
theorem derived9309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9309 := by
  apply localUnsat_implies_entails f9309 [c3238, c3329, c3634] c9309 unsat9309 (by rfl) a
  have h0 : Entails.eval a c3238 := h 3237 (by decide)
  have h1 : Entails.eval a c3329 := h 3328 (by decide)
  have h2 : Entails.eval a c3634 := h 3633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9310 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9308, some c7994, some c9193, some c9292, some c3244, some c3267, some c8269, some c9189, some c9309, some c3241, some c3259, some c3266, some c3269, some c4615, some c8412, some c3621, some c3375, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9310 : lratChecker f9310 p9310 = .success := by decide +kernel
theorem unsat9310 : Unsatisfiable (PosFin 65) f9310 := by
  apply lratCheckerSound f9310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9310
  · intro a ha; simp [p9310] at ha; subst a; trivial
  · exact checked9310
theorem derived9310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9310 := by
  apply localUnsat_implies_entails f9310 [c9308, c7994, c9193, c9292, c3244, c3267, c8269, c9189, c9309, c3241, c3259, c3266, c3269, c4615, c8412, c3621, c3375] c9310 unsat9310 (by rfl) a
  have h0 : Entails.eval a c9308 := derived9308 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9292 := derived9292 a h
  have h4 : Entails.eval a c3244 := h 3243 (by decide)
  have h5 : Entails.eval a c3267 := h 3266 (by decide)
  have h6 : Entails.eval a c8269 := derived8269 a h
  have h7 : Entails.eval a c9189 := derived9189 a h
  have h8 : Entails.eval a c9309 := derived9309 a h
  have h9 : Entails.eval a c3241 := h 3240 (by decide)
  have h10 : Entails.eval a c3259 := h 3258 (by decide)
  have h11 : Entails.eval a c3266 := h 3265 (by decide)
  have h12 : Entails.eval a c3269 := h 3268 (by decide)
  have h13 : Entails.eval a c4615 := h 4614 (by decide)
  have h14 : Entails.eval a c8412 := derived8412 a h
  have h15 : Entails.eval a c3621 := h 3620 (by decide)
  have h16 : Entails.eval a c3375 := h 3374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9311 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c8416, some c1424, some c4730, some c3622, some c3395, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9311 : lratChecker f9311 p9311 = .success := by decide +kernel
theorem unsat9311 : Unsatisfiable (PosFin 65) f9311 := by
  apply lratCheckerSound f9311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9311
  · intro a ha; simp [p9311] at ha; subst a; trivial
  · exact checked9311
theorem derived9311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9311 := by
  apply localUnsat_implies_entails f9311 [c8269, c8416, c1424, c4730, c3622, c3395] c9311 unsat9311 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c8416 := derived8416 a h
  have h2 : Entails.eval a c1424 := h 1423 (by decide)
  have h3 : Entails.eval a c4730 := h 4729 (by decide)
  have h4 : Entails.eval a c3622 := h 3621 (by decide)
  have h5 : Entails.eval a c3395 := h 3394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9312 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9292, some c9308, some c7994, some c9193, some c8269, some c9189, some c9309, some c9304, some c3244, some c3267, some c3241, some c3259, some c3266, some c9311, some c3809, some c3790, some c9310, some c9053, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9312 : lratChecker f9312 p9312 = .success := by decide +kernel
theorem unsat9312 : Unsatisfiable (PosFin 65) f9312 := by
  apply lratCheckerSound f9312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9312
  · intro a ha; simp [p9312] at ha; subst a; trivial
  · exact checked9312
theorem derived9312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9312 := by
  apply localUnsat_implies_entails f9312 [c9292, c9308, c7994, c9193, c8269, c9189, c9309, c9304, c3244, c3267, c3241, c3259, c3266, c9311, c3809, c3790, c9310, c9053] c9312 unsat9312 (by rfl) a
  have h0 : Entails.eval a c9292 := derived9292 a h
  have h1 : Entails.eval a c9308 := derived9308 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c9193 := derived9193 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c9189 := derived9189 a h
  have h6 : Entails.eval a c9309 := derived9309 a h
  have h7 : Entails.eval a c9304 := derived9304 a h
  have h8 : Entails.eval a c3244 := h 3243 (by decide)
  have h9 : Entails.eval a c3267 := h 3266 (by decide)
  have h10 : Entails.eval a c3241 := h 3240 (by decide)
  have h11 : Entails.eval a c3259 := h 3258 (by decide)
  have h12 : Entails.eval a c3266 := h 3265 (by decide)
  have h13 : Entails.eval a c9311 := derived9311 a h
  have h14 : Entails.eval a c3809 := h 3808 (by decide)
  have h15 : Entails.eval a c3790 := h 3789 (by decide)
  have h16 : Entails.eval a c9310 := derived9310 a h
  have h17 : Entails.eval a c9053 := derived9053 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9313 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3677, some c3374, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9313 : lratChecker f9313 p9313 = .success := by decide +kernel
theorem unsat9313 : Unsatisfiable (PosFin 65) f9313 := by
  apply lratCheckerSound f9313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9313
  · intro a ha; simp [p9313] at ha; subst a; trivial
  · exact checked9313
theorem derived9313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9313 := by
  apply localUnsat_implies_entails f9313 [c3677, c3374] c9313 unsat9313 (by rfl) a
  have h0 : Entails.eval a c3677 := h 3676 (by decide)
  have h1 : Entails.eval a c3374 := h 3373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9314 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9292, some c9193, some c9308, some c7994, some c8269, some c9189, some c9309, some c9304, some c9312, some c3645, some c3640, some c3649, some c3667, some c9296, some c3664, some c8409, some c9313, some c9245, some c9311, some c4628, some c3394, some c3621, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9314 : lratChecker f9314 p9314 = .success := by decide +kernel
theorem unsat9314 : Unsatisfiable (PosFin 65) f9314 := by
  apply lratCheckerSound f9314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9314
  · intro a ha; simp [p9314] at ha; subst a; trivial
  · exact checked9314
theorem derived9314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9314 := by
  apply localUnsat_implies_entails f9314 [c9292, c9193, c9308, c7994, c8269, c9189, c9309, c9304, c9312, c3645, c3640, c3649, c3667, c9296, c3664, c8409, c9313, c9245, c9311, c4628, c3394, c3621] c9314 unsat9314 (by rfl) a
  have h0 : Entails.eval a c9292 := derived9292 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9308 := derived9308 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c9189 := derived9189 a h
  have h6 : Entails.eval a c9309 := derived9309 a h
  have h7 : Entails.eval a c9304 := derived9304 a h
  have h8 : Entails.eval a c9312 := derived9312 a h
  have h9 : Entails.eval a c3645 := h 3644 (by decide)
  have h10 : Entails.eval a c3640 := h 3639 (by decide)
  have h11 : Entails.eval a c3649 := h 3648 (by decide)
  have h12 : Entails.eval a c3667 := h 3666 (by decide)
  have h13 : Entails.eval a c9296 := derived9296 a h
  have h14 : Entails.eval a c3664 := h 3663 (by decide)
  have h15 : Entails.eval a c8409 := derived8409 a h
  have h16 : Entails.eval a c9313 := derived9313 a h
  have h17 : Entails.eval a c9245 := derived9245 a h
  have h18 : Entails.eval a c9311 := derived9311 a h
  have h19 : Entails.eval a c4628 := h 4627 (by decide)
  have h20 : Entails.eval a c3394 := h 3393 (by decide)
  have h21 : Entails.eval a c3621 := h 3620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9315 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9314, some c9292, some c9193, some c1105, some c1106, some c2615, some c1118, some c1117, some c3110, some c3128, some c3678, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9315 : lratChecker f9315 p9315 = .success := by decide +kernel
theorem unsat9315 : Unsatisfiable (PosFin 65) f9315 := by
  apply lratCheckerSound f9315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9315
  · intro a ha; simp [p9315] at ha; subst a; trivial
  · exact checked9315
theorem derived9315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9315 := by
  apply localUnsat_implies_entails f9315 [c9314, c9292, c9193, c1105, c1106, c2615, c1118, c1117, c3110, c3128, c3678] c9315 unsat9315 (by rfl) a
  have h0 : Entails.eval a c9314 := derived9314 a h
  have h1 : Entails.eval a c9292 := derived9292 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c1105 := h 1104 (by decide)
  have h4 : Entails.eval a c1106 := h 1105 (by decide)
  have h5 : Entails.eval a c2615 := h 2614 (by decide)
  have h6 : Entails.eval a c1118 := h 1117 (by decide)
  have h7 : Entails.eval a c1117 := h 1116 (by decide)
  have h8 : Entails.eval a c3110 := h 3109 (by decide)
  have h9 : Entails.eval a c3128 := h 3127 (by decide)
  have h10 : Entails.eval a c3678 := h 3677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9316 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1092, some c1096, some c1102, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9316 : lratChecker f9316 p9316 = .success := by decide +kernel
theorem unsat9316 : Unsatisfiable (PosFin 65) f9316 := by
  apply lratCheckerSound f9316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9316
  · intro a ha; simp [p9316] at ha; subst a; trivial
  · exact checked9316
theorem derived9316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9316 := by
  apply localUnsat_implies_entails f9316 [c1092, c1096, c1102] c9316 unsat9316 (by rfl) a
  have h0 : Entails.eval a c1092 := h 1091 (by decide)
  have h1 : Entails.eval a c1096 := h 1095 (by decide)
  have h2 : Entails.eval a c1102 := h 1101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9317 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9314, some c9292, some c9193, some c9315, some c9316, some c1091, some c1090, some c1108, some c1102, some c2619, some c3112, some c3678, some c3128, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9317 : lratChecker f9317 p9317 = .success := by decide +kernel
theorem unsat9317 : Unsatisfiable (PosFin 65) f9317 := by
  apply lratCheckerSound f9317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9317
  · intro a ha; simp [p9317] at ha; subst a; trivial
  · exact checked9317
theorem derived9317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9317 := by
  apply localUnsat_implies_entails f9317 [c9314, c9292, c9193, c9315, c9316, c1091, c1090, c1108, c1102, c2619, c3112, c3678, c3128] c9317 unsat9317 (by rfl) a
  have h0 : Entails.eval a c9314 := derived9314 a h
  have h1 : Entails.eval a c9292 := derived9292 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9315 := derived9315 a h
  have h4 : Entails.eval a c9316 := derived9316 a h
  have h5 : Entails.eval a c1091 := h 1090 (by decide)
  have h6 : Entails.eval a c1090 := h 1089 (by decide)
  have h7 : Entails.eval a c1108 := h 1107 (by decide)
  have h8 : Entails.eval a c1102 := h 1101 (by decide)
  have h9 : Entails.eval a c2619 := h 2618 (by decide)
  have h10 : Entails.eval a c3112 := h 3111 (by decide)
  have h11 : Entails.eval a c3678 := h 3677 (by decide)
  have h12 : Entails.eval a c3128 := h 3127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9318 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨63, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2811, some c2614, some c3125, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9318 : lratChecker f9318 p9318 = .success := by decide +kernel
theorem unsat9318 : Unsatisfiable (PosFin 65) f9318 := by
  apply lratCheckerSound f9318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9318
  · intro a ha; simp [p9318] at ha; subst a; trivial
  · exact checked9318
theorem derived9318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9318 := by
  apply localUnsat_implies_entails f9318 [c2811, c2614, c3125] c9318 unsat9318 (by rfl) a
  have h0 : Entails.eval a c2811 := h 2810 (by decide)
  have h1 : Entails.eval a c2614 := h 2613 (by decide)
  have h2 : Entails.eval a c3125 := h 3124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9319 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨64, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9292, some c9314, some c7994, some c9318, some c1103, some c1114, some c2617, some c2812, some c3126, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9319 : lratChecker f9319 p9319 = .success := by decide +kernel
theorem unsat9319 : Unsatisfiable (PosFin 65) f9319 := by
  apply lratCheckerSound f9319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9319
  · intro a ha; simp [p9319] at ha; subst a; trivial
  · exact checked9319
theorem derived9319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9319 := by
  apply localUnsat_implies_entails f9319 [c9193, c9292, c9314, c7994, c9318, c1103, c1114, c2617, c2812, c3126] c9319 unsat9319 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9292 := derived9292 a h
  have h2 : Entails.eval a c9314 := derived9314 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9318 := derived9318 a h
  have h5 : Entails.eval a c1103 := h 1102 (by decide)
  have h6 : Entails.eval a c1114 := h 1113 (by decide)
  have h7 : Entails.eval a c2617 := h 2616 (by decide)
  have h8 : Entails.eval a c2812 := h 2811 (by decide)
  have h9 : Entails.eval a c3126 := h 3125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9320 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9314, some c9292, some c9193, some c7994, some c9319, some c2620, some c2815, some c3129, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9320 : lratChecker f9320 p9320 = .success := by decide +kernel
theorem unsat9320 : Unsatisfiable (PosFin 65) f9320 := by
  apply lratCheckerSound f9320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9320
  · intro a ha; simp [p9320] at ha; subst a; trivial
  · exact checked9320
theorem derived9320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9320 := by
  apply localUnsat_implies_entails f9320 [c9314, c9292, c9193, c7994, c9319, c2620, c2815, c3129] c9320 unsat9320 (by rfl) a
  have h0 : Entails.eval a c9314 := derived9314 a h
  have h1 : Entails.eval a c9292 := derived9292 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9319 := derived9319 a h
  have h5 : Entails.eval a c2620 := h 2619 (by decide)
  have h6 : Entails.eval a c2815 := h 2814 (by decide)
  have h7 : Entails.eval a c3129 := h 3128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9321 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9292, some c9314, some c9320, some c9317, some c9185, some c9172, some c1091, some c1090, some c1108, some c9119, some c3521, some c2619, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9321 : lratChecker f9321 p9321 = .success := by decide +kernel
theorem unsat9321 : Unsatisfiable (PosFin 65) f9321 := by
  apply lratCheckerSound f9321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9321
  · intro a ha; simp [p9321] at ha; subst a; trivial
  · exact checked9321
theorem derived9321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9321 := by
  apply localUnsat_implies_entails f9321 [c9292, c9314, c9320, c9317, c9185, c9172, c1091, c1090, c1108, c9119, c3521, c2619] c9321 unsat9321 (by rfl) a
  have h0 : Entails.eval a c9292 := derived9292 a h
  have h1 : Entails.eval a c9314 := derived9314 a h
  have h2 : Entails.eval a c9320 := derived9320 a h
  have h3 : Entails.eval a c9317 := derived9317 a h
  have h4 : Entails.eval a c9185 := derived9185 a h
  have h5 : Entails.eval a c9172 := derived9172 a h
  have h6 : Entails.eval a c1091 := h 1090 (by decide)
  have h7 : Entails.eval a c1090 := h 1089 (by decide)
  have h8 : Entails.eval a c1108 := h 1107 (by decide)
  have h9 : Entails.eval a c9119 := derived9119 a h
  have h10 : Entails.eval a c3521 := h 3520 (by decide)
  have h11 : Entails.eval a c2619 := h 2618 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9322 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9215, some c9210, some c3336, some c3245, some c4950, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9322 : lratChecker f9322 p9322 = .success := by decide +kernel
theorem unsat9322 : Unsatisfiable (PosFin 65) f9322 := by
  apply lratCheckerSound f9322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9322
  · intro a ha; simp [p9322] at ha; subst a; trivial
  · exact checked9322
theorem derived9322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9322 := by
  apply localUnsat_implies_entails f9322 [c9215, c9210, c3336, c3245, c4950] c9322 unsat9322 (by rfl) a
  have h0 : Entails.eval a c9215 := derived9215 a h
  have h1 : Entails.eval a c9210 := derived9210 a h
  have h2 : Entails.eval a c3336 := h 3335 (by decide)
  have h3 : Entails.eval a c3245 := h 3244 (by decide)
  have h4 : Entails.eval a c4950 := h 4949 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9323 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1143, some c1159, some c1160, some c1147, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9323 : lratChecker f9323 p9323 = .success := by decide +kernel
theorem unsat9323 : Unsatisfiable (PosFin 65) f9323 := by
  apply lratCheckerSound f9323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9323
  · intro a ha; simp [p9323] at ha; subst a; trivial
  · exact checked9323
theorem derived9323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9323 := by
  apply localUnsat_implies_entails f9323 [c1143, c1159, c1160, c1147] c9323 unsat9323 (by rfl) a
  have h0 : Entails.eval a c1143 := h 1142 (by decide)
  have h1 : Entails.eval a c1159 := h 1158 (by decide)
  have h2 : Entails.eval a c1160 := h 1159 (by decide)
  have h3 : Entails.eval a c1147 := h 1146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9324 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c3236, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9324 : lratChecker f9324 p9324 = .success := by decide +kernel
theorem unsat9324 : Unsatisfiable (PosFin 65) f9324 := by
  apply lratCheckerSound f9324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9324
  · intro a ha; simp [p9324] at ha; subst a; trivial
  · exact checked9324
theorem derived9324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9324 := by
  apply localUnsat_implies_entails f9324 [c9229, c3236] c9324 unsat9324 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c3236 := h 3235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9325 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨8, by decide⟩, true), (⟨62, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3246, some c9324, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9325 : lratChecker f9325 p9325 = .success := by decide +kernel
theorem unsat9325 : Unsatisfiable (PosFin 65) f9325 := by
  apply lratCheckerSound f9325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9325
  · intro a ha; simp [p9325] at ha; subst a; trivial
  · exact checked9325
theorem derived9325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9325 := by
  apply localUnsat_implies_entails f9325 [c3246, c9324] c9325 unsat9325 (by rfl) a
  have h0 : Entails.eval a c3246 := h 3245 (by decide)
  have h1 : Entails.eval a c9324 := derived9324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9326 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9321, some c9193, some c9307, some c9322, some c9323, some c9325, some c3235, some c3264, some c1157, some c3247, some c1155, some c9253, some c3236, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9326 : lratChecker f9326 p9326 = .success := by decide +kernel
theorem unsat9326 : Unsatisfiable (PosFin 65) f9326 := by
  apply lratCheckerSound f9326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9326
  · intro a ha; simp [p9326] at ha; subst a; trivial
  · exact checked9326
theorem derived9326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9326 := by
  apply localUnsat_implies_entails f9326 [c9321, c9193, c9307, c9322, c9323, c9325, c3235, c3264, c1157, c3247, c1155, c9253, c3236] c9326 unsat9326 (by rfl) a
  have h0 : Entails.eval a c9321 := derived9321 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9307 := derived9307 a h
  have h3 : Entails.eval a c9322 := derived9322 a h
  have h4 : Entails.eval a c9323 := derived9323 a h
  have h5 : Entails.eval a c9325 := derived9325 a h
  have h6 : Entails.eval a c3235 := h 3234 (by decide)
  have h7 : Entails.eval a c3264 := h 3263 (by decide)
  have h8 : Entails.eval a c1157 := h 1156 (by decide)
  have h9 : Entails.eval a c3247 := h 3246 (by decide)
  have h10 : Entails.eval a c1155 := h 1154 (by decide)
  have h11 : Entails.eval a c9253 := derived9253 a h
  have h12 : Entails.eval a c3236 := h 3235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9327 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9321, some c2730, some c1163, some c1150, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9327 : lratChecker f9327 p9327 = .success := by decide +kernel
theorem unsat9327 : Unsatisfiable (PosFin 65) f9327 := by
  apply lratCheckerSound f9327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9327
  · intro a ha; simp [p9327] at ha; subst a; trivial
  · exact checked9327
theorem derived9327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9327 := by
  apply localUnsat_implies_entails f9327 [c9321, c2730, c1163, c1150] c9327 unsat9327 (by rfl) a
  have h0 : Entails.eval a c9321 := derived9321 a h
  have h1 : Entails.eval a c2730 := h 2729 (by decide)
  have h2 : Entails.eval a c1163 := h 1162 (by decide)
  have h3 : Entails.eval a c1150 := h 1149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9328 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9321, some c9193, some c9307, some c9322, some c9323, some c9326, some c9327, some c8001, some c1166, some c2751, some c1158, some c2759, some c1164, some c1165, some c9253, some c1156, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9328 : lratChecker f9328 p9328 = .success := by decide +kernel
theorem unsat9328 : Unsatisfiable (PosFin 65) f9328 := by
  apply lratCheckerSound f9328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9328
  · intro a ha; simp [p9328] at ha; subst a; trivial
  · exact checked9328
theorem derived9328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9328 := by
  apply localUnsat_implies_entails f9328 [c9321, c9193, c9307, c9322, c9323, c9326, c9327, c8001, c1166, c2751, c1158, c2759, c1164, c1165, c9253, c1156] c9328 unsat9328 (by rfl) a
  have h0 : Entails.eval a c9321 := derived9321 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9307 := derived9307 a h
  have h3 : Entails.eval a c9322 := derived9322 a h
  have h4 : Entails.eval a c9323 := derived9323 a h
  have h5 : Entails.eval a c9326 := derived9326 a h
  have h6 : Entails.eval a c9327 := derived9327 a h
  have h7 : Entails.eval a c8001 := derived8001 a h
  have h8 : Entails.eval a c1166 := h 1165 (by decide)
  have h9 : Entails.eval a c2751 := h 2750 (by decide)
  have h10 : Entails.eval a c1158 := h 1157 (by decide)
  have h11 : Entails.eval a c2759 := h 2758 (by decide)
  have h12 : Entails.eval a c1164 := h 1163 (by decide)
  have h13 : Entails.eval a c1165 := h 1164 (by decide)
  have h14 : Entails.eval a c9253 := derived9253 a h
  have h15 : Entails.eval a c1156 := h 1155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9329 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8269, some c7994, some c9321, some c9193, some c9276, some c1151, some c1161, some c2731, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9329 : lratChecker f9329 p9329 = .success := by decide +kernel
theorem unsat9329 : Unsatisfiable (PosFin 65) f9329 := by
  apply lratCheckerSound f9329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9329
  · intro a ha; simp [p9329] at ha; subst a; trivial
  · exact checked9329
theorem derived9329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9329 := by
  apply localUnsat_implies_entails f9329 [c8269, c7994, c9321, c9193, c9276, c1151, c1161, c2731] c9329 unsat9329 (by rfl) a
  have h0 : Entails.eval a c8269 := derived8269 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c9321 := derived9321 a h
  have h3 : Entails.eval a c9193 := derived9193 a h
  have h4 : Entails.eval a c9276 := derived9276 a h
  have h5 : Entails.eval a c1151 := h 1150 (by decide)
  have h6 : Entails.eval a c1161 := h 1160 (by decide)
  have h7 : Entails.eval a c2731 := h 2730 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9330 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9328, some c7994, some c9321, some c9193, some c9329, some c9280, some c9049, some c2749, some c8380, some c1154, some c1167, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9330 : lratChecker f9330 p9330 = .success := by decide +kernel
theorem unsat9330 : Unsatisfiable (PosFin 65) f9330 := by
  apply lratCheckerSound f9330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9330
  · intro a ha; simp [p9330] at ha; subst a; trivial
  · exact checked9330
theorem derived9330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9330 := by
  apply localUnsat_implies_entails f9330 [c9328, c7994, c9321, c9193, c9329, c9280, c9049, c2749, c8380, c1154, c1167] c9330 unsat9330 (by rfl) a
  have h0 : Entails.eval a c9328 := derived9328 a h
  have h1 : Entails.eval a c7994 := derived7994 a h
  have h2 : Entails.eval a c9321 := derived9321 a h
  have h3 : Entails.eval a c9193 := derived9193 a h
  have h4 : Entails.eval a c9329 := derived9329 a h
  have h5 : Entails.eval a c9280 := derived9280 a h
  have h6 : Entails.eval a c9049 := derived9049 a h
  have h7 : Entails.eval a c2749 := h 2748 (by decide)
  have h8 : Entails.eval a c8380 := derived8380 a h
  have h9 : Entails.eval a c1154 := h 1153 (by decide)
  have h10 : Entails.eval a c1167 := h 1166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9331 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9321, some c9193, some c9328, some c7994, some c9330, some c9309, some c9304, some c9323, some c4948, some c3244, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9331 : lratChecker f9331 p9331 = .success := by decide +kernel
theorem unsat9331 : Unsatisfiable (PosFin 65) f9331 := by
  apply lratCheckerSound f9331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9331
  · intro a ha; simp [p9331] at ha; subst a; trivial
  · exact checked9331
theorem derived9331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9331 := by
  apply localUnsat_implies_entails f9331 [c9321, c9193, c9328, c7994, c9330, c9309, c9304, c9323, c4948, c3244] c9331 unsat9331 (by rfl) a
  have h0 : Entails.eval a c9321 := derived9321 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9328 := derived9328 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9330 := derived9330 a h
  have h5 : Entails.eval a c9309 := derived9309 a h
  have h6 : Entails.eval a c9304 := derived9304 a h
  have h7 : Entails.eval a c9323 := derived9323 a h
  have h8 : Entails.eval a c4948 := h 4947 (by decide)
  have h9 : Entails.eval a c3244 := h 3243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9332 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3223, some c2982, some c2981, some c2994, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p9332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9332 : lratChecker f9332 p9332 = .success := by decide +kernel
theorem unsat9332 : Unsatisfiable (PosFin 65) f9332 := by
  apply lratCheckerSound f9332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9332
  · intro a ha; simp [p9332] at ha; subst a; trivial
  · exact checked9332
theorem derived9332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9332 := by
  apply localUnsat_implies_entails f9332 [c3223, c2982, c2981, c2994] c9332 unsat9332 (by rfl) a
  have h0 : Entails.eval a c3223 := h 3222 (by decide)
  have h1 : Entails.eval a c2982 := h 2981 (by decide)
  have h2 : Entails.eval a c2981 := h 2980 (by decide)
  have h3 : Entails.eval a c2994 := h 2993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9333 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9321, some c9193, some c9331, some c9217, some c9323, some c9325, some c3235, some c9178, some c3022, some c1157, some c1158, some c3006, some c1155, some c1150, some c1168, some c9332, some c3213, some c3214, some c2985, some c8840, some c3217, some c1123, some c3233, some c1126, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked9333 : lratChecker f9333 p9333 = .success := by decide +kernel
theorem unsat9333 : Unsatisfiable (PosFin 65) f9333 := by
  apply lratCheckerSound f9333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9333
  · intro a ha; simp [p9333] at ha; subst a; trivial
  · exact checked9333
theorem derived9333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9333 := by
  apply localUnsat_implies_entails f9333 [c9321, c9193, c9331, c9217, c9323, c9325, c3235, c9178, c3022, c1157, c1158, c3006, c1155, c1150, c1168, c9332, c3213, c3214, c2985, c8840, c3217, c1123, c3233, c1126] c9333 unsat9333 (by rfl) a
  have h0 : Entails.eval a c9321 := derived9321 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9331 := derived9331 a h
  have h3 : Entails.eval a c9217 := derived9217 a h
  have h4 : Entails.eval a c9323 := derived9323 a h
  have h5 : Entails.eval a c9325 := derived9325 a h
  have h6 : Entails.eval a c3235 := h 3234 (by decide)
  have h7 : Entails.eval a c9178 := derived9178 a h
  have h8 : Entails.eval a c3022 := h 3021 (by decide)
  have h9 : Entails.eval a c1157 := h 1156 (by decide)
  have h10 : Entails.eval a c1158 := h 1157 (by decide)
  have h11 : Entails.eval a c3006 := h 3005 (by decide)
  have h12 : Entails.eval a c1155 := h 1154 (by decide)
  have h13 : Entails.eval a c1150 := h 1149 (by decide)
  have h14 : Entails.eval a c1168 := h 1167 (by decide)
  have h15 : Entails.eval a c9332 := derived9332 a h
  have h16 : Entails.eval a c3213 := h 3212 (by decide)
  have h17 : Entails.eval a c3214 := h 3213 (by decide)
  have h18 : Entails.eval a c2985 := h 2984 (by decide)
  have h19 : Entails.eval a c8840 := derived8840 a h
  have h20 : Entails.eval a c3217 := h 3216 (by decide)
  have h21 : Entails.eval a c1123 := h 1122 (by decide)
  have h22 : Entails.eval a c3233 := h 3232 (by decide)
  have h23 : Entails.eval a c1126 := h 1125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9334 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9331, some c9321, some c9193, some c9217, some c9323, some c9333, some c9327, some c8007, some c3021, some c2999, some c9178, some c2751, some c1158, some c3006, some c3024, some c2746, some c1170, some c1150, some c9273, some c2968, some c2719, some c2718, some c2985, some c2724, some c2974, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked9334 : lratChecker f9334 p9334 = .success := by decide +kernel
theorem unsat9334 : Unsatisfiable (PosFin 65) f9334 := by
  apply lratCheckerSound f9334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9334
  · intro a ha; simp [p9334] at ha; subst a; trivial
  · exact checked9334
theorem derived9334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9334 := by
  apply localUnsat_implies_entails f9334 [c9331, c9321, c9193, c9217, c9323, c9333, c9327, c8007, c3021, c2999, c9178, c2751, c1158, c3006, c3024, c2746, c1170, c1150, c9273, c2968, c2719, c2718, c2985, c2724, c2974] c9334 unsat9334 (by rfl) a
  have h0 : Entails.eval a c9331 := derived9331 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9217 := derived9217 a h
  have h4 : Entails.eval a c9323 := derived9323 a h
  have h5 : Entails.eval a c9333 := derived9333 a h
  have h6 : Entails.eval a c9327 := derived9327 a h
  have h7 : Entails.eval a c8007 := derived8007 a h
  have h8 : Entails.eval a c3021 := h 3020 (by decide)
  have h9 : Entails.eval a c2999 := h 2998 (by decide)
  have h10 : Entails.eval a c9178 := derived9178 a h
  have h11 : Entails.eval a c2751 := h 2750 (by decide)
  have h12 : Entails.eval a c1158 := h 1157 (by decide)
  have h13 : Entails.eval a c3006 := h 3005 (by decide)
  have h14 : Entails.eval a c3024 := h 3023 (by decide)
  have h15 : Entails.eval a c2746 := h 2745 (by decide)
  have h16 : Entails.eval a c1170 := h 1169 (by decide)
  have h17 : Entails.eval a c1150 := h 1149 (by decide)
  have h18 : Entails.eval a c9273 := derived9273 a h
  have h19 : Entails.eval a c2968 := h 2967 (by decide)
  have h20 : Entails.eval a c2719 := h 2718 (by decide)
  have h21 : Entails.eval a c2718 := h 2717 (by decide)
  have h22 : Entails.eval a c2985 := h 2984 (by decide)
  have h23 : Entails.eval a c2724 := h 2723 (by decide)
  have h24 : Entails.eval a c2974 := h 2973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9335 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9331, some c9321, some c9193, some c9334, some c3005, some c3000, some c3002, some c1158, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9335 : lratChecker f9335 p9335 = .success := by decide +kernel
theorem unsat9335 : Unsatisfiable (PosFin 65) f9335 := by
  apply lratCheckerSound f9335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9335
  · intro a ha; simp [p9335] at ha; subst a; trivial
  · exact checked9335
theorem derived9335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9335 := by
  apply localUnsat_implies_entails f9335 [c9331, c9321, c9193, c9334, c3005, c3000, c3002, c1158] c9335 unsat9335 (by rfl) a
  have h0 : Entails.eval a c9331 := derived9331 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9334 := derived9334 a h
  have h4 : Entails.eval a c3005 := h 3004 (by decide)
  have h5 : Entails.eval a c3000 := h 2999 (by decide)
  have h6 : Entails.eval a c3002 := h 3001 (by decide)
  have h7 : Entails.eval a c1158 := h 1157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9336 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9321, some c9193, some c9331, some c9335, some c7994, some c8269, some c3009, some c1172, some c3003, some c1170, some c2166, some c2736, some c3282, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9336 : lratChecker f9336 p9336 = .success := by decide +kernel
theorem unsat9336 : Unsatisfiable (PosFin 65) f9336 := by
  apply lratCheckerSound f9336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9336
  · intro a ha; simp [p9336] at ha; subst a; trivial
  · exact checked9336
theorem derived9336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9336 := by
  apply localUnsat_implies_entails f9336 [c9321, c9193, c9331, c9335, c7994, c8269, c3009, c1172, c3003, c1170, c2166, c2736, c3282] c9336 unsat9336 (by rfl) a
  have h0 : Entails.eval a c9321 := derived9321 a h
  have h1 : Entails.eval a c9193 := derived9193 a h
  have h2 : Entails.eval a c9331 := derived9331 a h
  have h3 : Entails.eval a c9335 := derived9335 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c3009 := h 3008 (by decide)
  have h7 : Entails.eval a c1172 := h 1171 (by decide)
  have h8 : Entails.eval a c3003 := h 3002 (by decide)
  have h9 : Entails.eval a c1170 := h 1169 (by decide)
  have h10 : Entails.eval a c2166 := h 2165 (by decide)
  have h11 : Entails.eval a c2736 := h 2735 (by decide)
  have h12 : Entails.eval a c3282 := h 3281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9337 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9336, some c9321, some c9193, some c1162, some c1106, some c2618, some c2813, some c3127, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9337 : lratChecker f9337 p9337 = .success := by decide +kernel
theorem unsat9337 : Unsatisfiable (PosFin 65) f9337 := by
  apply lratCheckerSound f9337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9337
  · intro a ha; simp [p9337] at ha; subst a; trivial
  · exact checked9337
theorem derived9337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9337 := by
  apply localUnsat_implies_entails f9337 [c9336, c9321, c9193, c1162, c1106, c2618, c2813, c3127] c9337 unsat9337 (by rfl) a
  have h0 : Entails.eval a c9336 := derived9336 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c1162 := h 1161 (by decide)
  have h4 : Entails.eval a c1106 := h 1105 (by decide)
  have h5 : Entails.eval a c2618 := h 2617 (by decide)
  have h6 : Entails.eval a c2813 := h 2812 (by decide)
  have h7 : Entails.eval a c3127 := h 3126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9338 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9336, some c9321, some c9193, some c9337, some c9262, some c9316, some c9323, some c1142, some c9147, some c1108, some c9178, some c1157, some c1158, some c9195, some c1168, some c8496, some c8580, some c1107, some c8846, some c1122, some c1123, some c1170, some c685, some c590, some c8609, some c8583, some c9050, some c3103, some c3104, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked9338 : lratChecker f9338 p9338 = .success := by decide +kernel
theorem unsat9338 : Unsatisfiable (PosFin 65) f9338 := by
  apply lratCheckerSound f9338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9338
  · intro a ha; simp [p9338] at ha; subst a; trivial
  · exact checked9338
theorem derived9338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9338 := by
  apply localUnsat_implies_entails f9338 [c9336, c9321, c9193, c9337, c9262, c9316, c9323, c1142, c9147, c1108, c9178, c1157, c1158, c9195, c1168, c8496, c8580, c1107, c8846, c1122, c1123, c1170, c685, c590, c8609, c8583, c9050, c3103, c3104] c9338 unsat9338 (by rfl) a
  have h0 : Entails.eval a c9336 := derived9336 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9337 := derived9337 a h
  have h4 : Entails.eval a c9262 := derived9262 a h
  have h5 : Entails.eval a c9316 := derived9316 a h
  have h6 : Entails.eval a c9323 := derived9323 a h
  have h7 : Entails.eval a c1142 := h 1141 (by decide)
  have h8 : Entails.eval a c9147 := derived9147 a h
  have h9 : Entails.eval a c1108 := h 1107 (by decide)
  have h10 : Entails.eval a c9178 := derived9178 a h
  have h11 : Entails.eval a c1157 := h 1156 (by decide)
  have h12 : Entails.eval a c1158 := h 1157 (by decide)
  have h13 : Entails.eval a c9195 := derived9195 a h
  have h14 : Entails.eval a c1168 := h 1167 (by decide)
  have h15 : Entails.eval a c8496 := derived8496 a h
  have h16 : Entails.eval a c8580 := derived8580 a h
  have h17 : Entails.eval a c1107 := h 1106 (by decide)
  have h18 : Entails.eval a c8846 := derived8846 a h
  have h19 : Entails.eval a c1122 := h 1121 (by decide)
  have h20 : Entails.eval a c1123 := h 1122 (by decide)
  have h21 : Entails.eval a c1170 := h 1169 (by decide)
  have h22 : Entails.eval a c685 := h 684 (by decide)
  have h23 : Entails.eval a c590 := h 589 (by decide)
  have h24 : Entails.eval a c8609 := derived8609 a h
  have h25 : Entails.eval a c8583 := derived8583 a h
  have h26 : Entails.eval a c9050 := derived9050 a h
  have h27 : Entails.eval a c3103 := h 3102 (by decide)
  have h28 : Entails.eval a c3104 := h 3103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9339 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2613, some c2731, some c3109, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9339 : lratChecker f9339 p9339 = .success := by decide +kernel
theorem unsat9339 : Unsatisfiable (PosFin 65) f9339 := by
  apply lratCheckerSound f9339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9339
  · intro a ha; simp [p9339] at ha; subst a; trivial
  · exact checked9339
theorem derived9339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9339 := by
  apply localUnsat_implies_entails f9339 [c2613, c2731, c3109] c9339 unsat9339 (by rfl) a
  have h0 : Entails.eval a c2613 := h 2612 (by decide)
  have h1 : Entails.eval a c2731 := h 2730 (by decide)
  have h2 : Entails.eval a c3109 := h 3108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9340 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨63, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1151, some c9049, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9340 : lratChecker f9340 p9340 = .success := by decide +kernel
theorem unsat9340 : Unsatisfiable (PosFin 65) f9340 := by
  apply lratCheckerSound f9340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9340
  · intro a ha; simp [p9340] at ha; subst a; trivial
  · exact checked9340
theorem derived9340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9340 := by
  apply localUnsat_implies_entails f9340 [c1151, c9049] c9340 unsat9340 (by rfl) a
  have h0 : Entails.eval a c1151 := h 1150 (by decide)
  have h1 : Entails.eval a c9049 := derived9049 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9341 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9336, some c9321, some c9193, some c9338, some c7994, some c9289, some c9339, some c9340, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9341 : lratChecker f9341 p9341 = .success := by decide +kernel
theorem unsat9341 : Unsatisfiable (PosFin 65) f9341 := by
  apply lratCheckerSound f9341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9341
  · intro a ha; simp [p9341] at ha; subst a; trivial
  · exact checked9341
theorem derived9341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9341 := by
  apply localUnsat_implies_entails f9341 [c9336, c9321, c9193, c9338, c7994, c9289, c9339, c9340] c9341 unsat9341 (by rfl) a
  have h0 : Entails.eval a c9336 := derived9336 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9338 := derived9338 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c9289 := derived9289 a h
  have h6 : Entails.eval a c9339 := derived9339 a h
  have h7 : Entails.eval a c9340 := derived9340 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9342 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, true), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2734, some c2615, some c3110, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9342 : lratChecker f9342 p9342 = .success := by decide +kernel
theorem unsat9342 : Unsatisfiable (PosFin 65) f9342 := by
  apply lratCheckerSound f9342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9342
  · intro a ha; simp [p9342] at ha; subst a; trivial
  · exact checked9342
theorem derived9342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9342 := by
  apply localUnsat_implies_entails f9342 [c2734, c2615, c3110] c9342 unsat9342 (by rfl) a
  have h0 : Entails.eval a c2734 := h 2733 (by decide)
  have h1 : Entails.eval a c2615 := h 2614 (by decide)
  have h2 : Entails.eval a c3110 := h 3109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9343 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9336, some c9321, some c9193, some c9342, some c9316, some c9323, some c1142, some c1108, some c1158, some c2738, some c2619, some c3112, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9343 : lratChecker f9343 p9343 = .success := by decide +kernel
theorem unsat9343 : Unsatisfiable (PosFin 65) f9343 := by
  apply lratCheckerSound f9343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9343
  · intro a ha; simp [p9343] at ha; subst a; trivial
  · exact checked9343
theorem derived9343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9343 := by
  apply localUnsat_implies_entails f9343 [c9336, c9321, c9193, c9342, c9316, c9323, c1142, c1108, c1158, c2738, c2619, c3112] c9343 unsat9343 (by rfl) a
  have h0 : Entails.eval a c9336 := derived9336 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9193 := derived9193 a h
  have h3 : Entails.eval a c9342 := derived9342 a h
  have h4 : Entails.eval a c9316 := derived9316 a h
  have h5 : Entails.eval a c9323 := derived9323 a h
  have h6 : Entails.eval a c1142 := h 1141 (by decide)
  have h7 : Entails.eval a c1108 := h 1107 (by decide)
  have h8 : Entails.eval a c1158 := h 1157 (by decide)
  have h9 : Entails.eval a c2738 := h 2737 (by decide)
  have h10 : Entails.eval a c2619 := h 2618 (by decide)
  have h11 : Entails.eval a c3112 := h 3111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9344 : DefaultClause 65 := directClause [(⟨64, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9336, some c9321, some c7994, some c9289, some c9340, some c1152, some c8300, some c1154, some c1111, some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9344 : lratChecker f9344 p9344 = .success := by decide +kernel
theorem unsat9344 : Unsatisfiable (PosFin 65) f9344 := by
  apply lratCheckerSound f9344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9344
  · intro a ha; simp [p9344] at ha; subst a; trivial
  · exact checked9344
theorem derived9344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9344 := by
  apply localUnsat_implies_entails f9344 [c9336, c9321, c7994, c9289, c9340, c1152, c8300, c1154, c1111] c9344 unsat9344 (by rfl) a
  have h0 : Entails.eval a c9336 := derived9336 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c9289 := derived9289 a h
  have h4 : Entails.eval a c9340 := derived9340 a h
  have h5 : Entails.eval a c1152 := h 1151 (by decide)
  have h6 : Entails.eval a c8300 := derived8300 a h
  have h7 : Entails.eval a c1154 := h 1153 (by decide)
  have h8 : Entails.eval a c1111 := h 1110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9345 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9344, some c9343, some c9341, some c9336, some c9337, some c9316, some c9147, some c9321, some c9323, some c1142, some c1108, some c9269, some c1157, some c9262, some c9193, some c9339, some c1171, some c1153, some c1168, some c9178, some c3098, some c3105, some c2936, some c1067, some c592, some c1128, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked9345 : lratChecker f9345 p9345 = .success := by decide +kernel
theorem unsat9345 : Unsatisfiable (PosFin 65) f9345 := by
  apply lratCheckerSound f9345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9345
  · intro a ha; simp [p9345] at ha; subst a; trivial
  · exact checked9345
theorem derived9345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9345 := by
  apply localUnsat_implies_entails f9345 [c9344, c9343, c9341, c9336, c9337, c9316, c9147, c9321, c9323, c1142, c1108, c9269, c1157, c9262, c9193, c9339, c1171, c1153, c1168, c9178, c3098, c3105, c2936, c1067, c592, c1128] c9345 unsat9345 (by rfl) a
  have h0 : Entails.eval a c9344 := derived9344 a h
  have h1 : Entails.eval a c9343 := derived9343 a h
  have h2 : Entails.eval a c9341 := derived9341 a h
  have h3 : Entails.eval a c9336 := derived9336 a h
  have h4 : Entails.eval a c9337 := derived9337 a h
  have h5 : Entails.eval a c9316 := derived9316 a h
  have h6 : Entails.eval a c9147 := derived9147 a h
  have h7 : Entails.eval a c9321 := derived9321 a h
  have h8 : Entails.eval a c9323 := derived9323 a h
  have h9 : Entails.eval a c1142 := h 1141 (by decide)
  have h10 : Entails.eval a c1108 := h 1107 (by decide)
  have h11 : Entails.eval a c9269 := derived9269 a h
  have h12 : Entails.eval a c1157 := h 1156 (by decide)
  have h13 : Entails.eval a c9262 := derived9262 a h
  have h14 : Entails.eval a c9193 := derived9193 a h
  have h15 : Entails.eval a c9339 := derived9339 a h
  have h16 : Entails.eval a c1171 := h 1170 (by decide)
  have h17 : Entails.eval a c1153 := h 1152 (by decide)
  have h18 : Entails.eval a c1168 := h 1167 (by decide)
  have h19 : Entails.eval a c9178 := derived9178 a h
  have h20 : Entails.eval a c3098 := h 3097 (by decide)
  have h21 : Entails.eval a c3105 := h 3104 (by decide)
  have h22 : Entails.eval a c2936 := h 2935 (by decide)
  have h23 : Entails.eval a c1067 := h 1066 (by decide)
  have h24 : Entails.eval a c592 := h 591 (by decide)
  have h25 : Entails.eval a c1128 := h 1127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9346 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9344, some c9343, some c9336, some c9337, some c9316, some c9147, some c9178, some c9321, some c9323, some c1142, some c1108, some c9262, some c9341, some c9193, some c9269, some c9345, some c2605, some c2606, some c741, some c1128, some c1071, some c597, some c9267, some c3272, some c3277, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked9346 : lratChecker f9346 p9346 = .success := by decide +kernel
theorem unsat9346 : Unsatisfiable (PosFin 65) f9346 := by
  apply lratCheckerSound f9346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9346
  · intro a ha; simp [p9346] at ha; subst a; trivial
  · exact checked9346
theorem derived9346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9346 := by
  apply localUnsat_implies_entails f9346 [c9344, c9343, c9336, c9337, c9316, c9147, c9178, c9321, c9323, c1142, c1108, c9262, c9341, c9193, c9269, c9345, c2605, c2606, c741, c1128, c1071, c597, c9267, c3272, c3277] c9346 unsat9346 (by rfl) a
  have h0 : Entails.eval a c9344 := derived9344 a h
  have h1 : Entails.eval a c9343 := derived9343 a h
  have h2 : Entails.eval a c9336 := derived9336 a h
  have h3 : Entails.eval a c9337 := derived9337 a h
  have h4 : Entails.eval a c9316 := derived9316 a h
  have h5 : Entails.eval a c9147 := derived9147 a h
  have h6 : Entails.eval a c9178 := derived9178 a h
  have h7 : Entails.eval a c9321 := derived9321 a h
  have h8 : Entails.eval a c9323 := derived9323 a h
  have h9 : Entails.eval a c1142 := h 1141 (by decide)
  have h10 : Entails.eval a c1108 := h 1107 (by decide)
  have h11 : Entails.eval a c9262 := derived9262 a h
  have h12 : Entails.eval a c9341 := derived9341 a h
  have h13 : Entails.eval a c9193 := derived9193 a h
  have h14 : Entails.eval a c9269 := derived9269 a h
  have h15 : Entails.eval a c9345 := derived9345 a h
  have h16 : Entails.eval a c2605 := h 2604 (by decide)
  have h17 : Entails.eval a c2606 := h 2605 (by decide)
  have h18 : Entails.eval a c741 := h 740 (by decide)
  have h19 : Entails.eval a c1128 := h 1127 (by decide)
  have h20 : Entails.eval a c1071 := h 1070 (by decide)
  have h21 : Entails.eval a c597 := h 596 (by decide)
  have h22 : Entails.eval a c9267 := derived9267 a h
  have h23 : Entails.eval a c3272 := h 3271 (by decide)
  have h24 : Entails.eval a c3277 := h 3276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9347 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9193, some c9321, some c9336, some c9344, some c9343, some c9337, some c9262, some c9316, some c9323, some c9339, some c1142, some c9147, some c1171, some c1108, some c9178, some c9346, some c9273, some c2718, some c1128, some c9267, some c9274, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9347 : lratChecker f9347 p9347 = .success := by decide +kernel
theorem unsat9347 : Unsatisfiable (PosFin 65) f9347 := by
  apply lratCheckerSound f9347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9347
  · intro a ha; simp [p9347] at ha; subst a; trivial
  · exact checked9347
theorem derived9347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9347 := by
  apply localUnsat_implies_entails f9347 [c9193, c9321, c9336, c9344, c9343, c9337, c9262, c9316, c9323, c9339, c1142, c9147, c1171, c1108, c9178, c9346, c9273, c2718, c1128, c9267, c9274] c9347 unsat9347 (by rfl) a
  have h0 : Entails.eval a c9193 := derived9193 a h
  have h1 : Entails.eval a c9321 := derived9321 a h
  have h2 : Entails.eval a c9336 := derived9336 a h
  have h3 : Entails.eval a c9344 := derived9344 a h
  have h4 : Entails.eval a c9343 := derived9343 a h
  have h5 : Entails.eval a c9337 := derived9337 a h
  have h6 : Entails.eval a c9262 := derived9262 a h
  have h7 : Entails.eval a c9316 := derived9316 a h
  have h8 : Entails.eval a c9323 := derived9323 a h
  have h9 : Entails.eval a c9339 := derived9339 a h
  have h10 : Entails.eval a c1142 := h 1141 (by decide)
  have h11 : Entails.eval a c9147 := derived9147 a h
  have h12 : Entails.eval a c1171 := h 1170 (by decide)
  have h13 : Entails.eval a c1108 := h 1107 (by decide)
  have h14 : Entails.eval a c9178 := derived9178 a h
  have h15 : Entails.eval a c9346 := derived9346 a h
  have h16 : Entails.eval a c9273 := derived9273 a h
  have h17 : Entails.eval a c2718 := h 2717 (by decide)
  have h18 : Entails.eval a c1128 := h 1127 (by decide)
  have h19 : Entails.eval a c9267 := derived9267 a h
  have h20 : Entails.eval a c9274 := derived9274 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9348 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨7, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3190, some c4854, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9348 : lratChecker f9348 p9348 = .success := by decide +kernel
theorem unsat9348 : Unsatisfiable (PosFin 65) f9348 := by
  apply lratCheckerSound f9348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9348
  · intro a ha; simp [p9348] at ha; subst a; trivial
  · exact checked9348
theorem derived9348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9348 := by
  apply localUnsat_implies_entails f9348 [c3190, c4854] c9348 unsat9348 (by rfl) a
  have h0 : Entails.eval a c3190 := h 3189 (by decide)
  have h1 : Entails.eval a c4854 := h 4853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9349 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨58, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3165, some c2888, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9349 : lratChecker f9349 p9349 = .success := by decide +kernel
theorem unsat9349 : Unsatisfiable (PosFin 65) f9349 := by
  apply lratCheckerSound f9349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9349
  · intro a ha; simp [p9349] at ha; subst a; trivial
  · exact checked9349
theorem derived9349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9349 := by
  apply localUnsat_implies_entails f9349 [c3165, c2888] c9349 unsat9349 (by rfl) a
  have h0 : Entails.eval a c3165 := h 3164 (by decide)
  have h1 : Entails.eval a c2888 := h 2887 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9350 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9103, some c9348, some c3153, some c2889, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9350 : lratChecker f9350 p9350 = .success := by decide +kernel
theorem unsat9350 : Unsatisfiable (PosFin 65) f9350 := by
  apply lratCheckerSound f9350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9350
  · intro a ha; simp [p9350] at ha; subst a; trivial
  · exact checked9350
theorem derived9350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9350 := by
  apply localUnsat_implies_entails f9350 [c9103, c9348, c3153, c2889] c9350 unsat9350 (by rfl) a
  have h0 : Entails.eval a c9103 := derived9103 a h
  have h1 : Entails.eval a c9348 := derived9348 a h
  have h2 : Entails.eval a c3153 := h 3152 (by decide)
  have h3 : Entails.eval a c2889 := h 2888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9350

end CochromaticTwenty.Certificates.FixedCore0
