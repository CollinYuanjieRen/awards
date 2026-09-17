import MerLeanExperiment.Certificates.FixedCore1.Steps1400_1499

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7381 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1711, some c128, some c7380, some c3151, some c3147, some c6753, some c3149, some c3144, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7381 : lratChecker f7381 p7381 = .success := by decide +kernel
theorem unsat7381 : Unsatisfiable (PosFin 65) f7381 := by
  apply lratCheckerSound f7381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7381
  · intro a ha; simp [p7381] at ha; subst a; trivial
  · exact checked7381
theorem derived7381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7381 := by
  apply localUnsat_implies_entails f7381 [c1711, c128, c7380, c3151, c3147, c6753, c3149, c3144] c7381 unsat7381 (by rfl) a
  have h0 : Entails.eval a c1711 := h 1710 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c7380 := derived7380 a h
  have h3 : Entails.eval a c3151 := h 3150 (by decide)
  have h4 : Entails.eval a c3147 := h 3146 (by decide)
  have h5 : Entails.eval a c6753 := derived6753 a h
  have h6 : Entails.eval a c3149 := h 3148 (by decide)
  have h7 : Entails.eval a c3144 := h 3143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7382 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1774, some c1768, some c1436, some c1429, some c1435, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7382 : lratChecker f7382 p7382 = .success := by decide +kernel
theorem unsat7382 : Unsatisfiable (PosFin 65) f7382 := by
  apply lratCheckerSound f7382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7382
  · intro a ha; simp [p7382] at ha; subst a; trivial
  · exact checked7382
theorem derived7382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7382 := by
  apply localUnsat_implies_entails f7382 [c1774, c1768, c1436, c1429, c1435] c7382 unsat7382 (by rfl) a
  have h0 : Entails.eval a c1774 := h 1773 (by decide)
  have h1 : Entails.eval a c1768 := h 1767 (by decide)
  have h2 : Entails.eval a c1436 := h 1435 (by decide)
  have h3 : Entails.eval a c1429 := h 1428 (by decide)
  have h4 : Entails.eval a c1435 := h 1434 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7383 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7356, some c7376, some c7377, some c7378, some c7370, some c7379, some c7381, some c7323, some c7382, some c226, some c218, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7383 : lratChecker f7383 p7383 = .success := by decide +kernel
theorem unsat7383 : Unsatisfiable (PosFin 65) f7383 := by
  apply lratCheckerSound f7383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7383
  · intro a ha; simp [p7383] at ha; subst a; trivial
  · exact checked7383
theorem derived7383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7383 := by
  apply localUnsat_implies_entails f7383 [c7339, c7356, c7376, c7377, c7378, c7370, c7379, c7381, c7323, c7382, c226, c218] c7383 unsat7383 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  have h2 : Entails.eval a c7376 := derived7376 a h
  have h3 : Entails.eval a c7377 := derived7377 a h
  have h4 : Entails.eval a c7378 := derived7378 a h
  have h5 : Entails.eval a c7370 := derived7370 a h
  have h6 : Entails.eval a c7379 := derived7379 a h
  have h7 : Entails.eval a c7381 := derived7381 a h
  have h8 : Entails.eval a c7323 := derived7323 a h
  have h9 : Entails.eval a c7382 := derived7382 a h
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7384 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7377, some c7247, some c793, some c1793, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7384 : lratChecker f7384 p7384 = .success := by decide +kernel
theorem unsat7384 : Unsatisfiable (PosFin 65) f7384 := by
  apply lratCheckerSound f7384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7384
  · intro a ha; simp [p7384] at ha; subst a; trivial
  · exact checked7384
theorem derived7384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7384 := by
  apply localUnsat_implies_entails f7384 [c7377, c7247, c793, c1793] c7384 unsat7384 (by rfl) a
  have h0 : Entails.eval a c7377 := derived7377 a h
  have h1 : Entails.eval a c7247 := derived7247 a h
  have h2 : Entails.eval a c793 := h 792 (by decide)
  have h3 : Entails.eval a c1793 := h 1792 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7385 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1287, some c7373, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7385 : lratChecker f7385 p7385 = .success := by decide +kernel
theorem unsat7385 : Unsatisfiable (PosFin 65) f7385 := by
  apply lratCheckerSound f7385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7385
  · intro a ha; simp [p7385] at ha; subst a; trivial
  · exact checked7385
theorem derived7385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7385 := by
  apply localUnsat_implies_entails f7385 [c1287, c7373] c7385 unsat7385 (by rfl) a
  have h0 : Entails.eval a c1287 := h 1286 (by decide)
  have h1 : Entails.eval a c7373 := derived7373 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7386 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7356, some c7376, some c7377, some c7383, some c7384, some c7385, some c7379, some c7381, some c7308, some c7382, some c226, some c218, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7386 : lratChecker f7386 p7386 = .success := by decide +kernel
theorem unsat7386 : Unsatisfiable (PosFin 65) f7386 := by
  apply lratCheckerSound f7386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7386
  · intro a ha; simp [p7386] at ha; subst a; trivial
  · exact checked7386
theorem derived7386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7386 := by
  apply localUnsat_implies_entails f7386 [c7339, c7356, c7376, c7377, c7383, c7384, c7385, c7379, c7381, c7308, c7382, c226, c218] c7386 unsat7386 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  have h2 : Entails.eval a c7376 := derived7376 a h
  have h3 : Entails.eval a c7377 := derived7377 a h
  have h4 : Entails.eval a c7383 := derived7383 a h
  have h5 : Entails.eval a c7384 := derived7384 a h
  have h6 : Entails.eval a c7385 := derived7385 a h
  have h7 : Entails.eval a c7379 := derived7379 a h
  have h8 : Entails.eval a c7381 := derived7381 a h
  have h9 : Entails.eval a c7308 := derived7308 a h
  have h10 : Entails.eval a c7382 := derived7382 a h
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7387 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c269, some c7247, some c284, some c750, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7387 : lratChecker f7387 p7387 = .success := by decide +kernel
theorem unsat7387 : Unsatisfiable (PosFin 65) f7387 := by
  apply lratCheckerSound f7387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7387
  · intro a ha; simp [p7387] at ha; subst a; trivial
  · exact checked7387
theorem derived7387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7387 := by
  apply localUnsat_implies_entails f7387 [c269, c7247, c284, c750] c7387 unsat7387 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c7247 := derived7247 a h
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7388 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7377, some c7355, some c7387, some c7323, some c1760, some c694, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7388 : lratChecker f7388 p7388 = .success := by decide +kernel
theorem unsat7388 : Unsatisfiable (PosFin 65) f7388 := by
  apply lratCheckerSound f7388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7388
  · intro a ha; simp [p7388] at ha; subst a; trivial
  · exact checked7388
theorem derived7388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7388 := by
  apply localUnsat_implies_entails f7388 [c7377, c7355, c7387, c7323, c1760, c694] c7388 unsat7388 (by rfl) a
  have h0 : Entails.eval a c7377 := derived7377 a h
  have h1 : Entails.eval a c7355 := derived7355 a h
  have h2 : Entails.eval a c7387 := derived7387 a h
  have h3 : Entails.eval a c7323 := derived7323 a h
  have h4 : Entails.eval a c1760 := h 1759 (by decide)
  have h5 : Entails.eval a c694 := h 693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7389 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7377, some c269, some c7247, some c284, some c788, some c1789, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7389 : lratChecker f7389 p7389 = .success := by decide +kernel
theorem unsat7389 : Unsatisfiable (PosFin 65) f7389 := by
  apply lratCheckerSound f7389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7389
  · intro a ha; simp [p7389] at ha; subst a; trivial
  · exact checked7389
theorem derived7389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7389 := by
  apply localUnsat_implies_entails f7389 [c7377, c269, c7247, c284, c788, c1789] c7389 unsat7389 (by rfl) a
  have h0 : Entails.eval a c7377 := derived7377 a h
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c7247 := derived7247 a h
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c788 := h 787 (by decide)
  have h5 : Entails.eval a c1789 := h 1788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7390 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1283, some c7222, some c1593, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7390 : lratChecker f7390 p7390 = .success := by decide +kernel
theorem unsat7390 : Unsatisfiable (PosFin 65) f7390 := by
  apply lratCheckerSound f7390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7390
  · intro a ha; simp [p7390] at ha; subst a; trivial
  · exact checked7390
theorem derived7390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7390 := by
  apply localUnsat_implies_entails f7390 [c1283, c7222, c1593] c7390 unsat7390 (by rfl) a
  have h0 : Entails.eval a c1283 := h 1282 (by decide)
  have h1 : Entails.eval a c7222 := derived7222 a h
  have h2 : Entails.eval a c1593 := h 1592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7391 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1707, some c1760, some c1964, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p7391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7391 : lratChecker f7391 p7391 = .success := by decide +kernel
theorem unsat7391 : Unsatisfiable (PosFin 65) f7391 := by
  apply lratCheckerSound f7391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7391
  · intro a ha; simp [p7391] at ha; subst a; trivial
  · exact checked7391
theorem derived7391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7391 := by
  apply localUnsat_implies_entails f7391 [c1707, c1760, c1964] c7391 unsat7391 (by rfl) a
  have h0 : Entails.eval a c1707 := h 1706 (by decide)
  have h1 : Entails.eval a c1760 := h 1759 (by decide)
  have h2 : Entails.eval a c1964 := h 1963 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7392 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7356, some c7376, some c7377, some c7386, some c7388, some c7389, some c7390, some c7391, some c7308, some c7382, some c226, some c218, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7392 : lratChecker f7392 p7392 = .success := by decide +kernel
theorem unsat7392 : Unsatisfiable (PosFin 65) f7392 := by
  apply lratCheckerSound f7392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7392
  · intro a ha; simp [p7392] at ha; subst a; trivial
  · exact checked7392
theorem derived7392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7392 := by
  apply localUnsat_implies_entails f7392 [c7339, c7356, c7376, c7377, c7386, c7388, c7389, c7390, c7391, c7308, c7382, c226, c218] c7392 unsat7392 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  have h2 : Entails.eval a c7376 := derived7376 a h
  have h3 : Entails.eval a c7377 := derived7377 a h
  have h4 : Entails.eval a c7386 := derived7386 a h
  have h5 : Entails.eval a c7388 := derived7388 a h
  have h6 : Entails.eval a c7389 := derived7389 a h
  have h7 : Entails.eval a c7390 := derived7390 a h
  have h8 : Entails.eval a c7391 := derived7391 a h
  have h9 : Entails.eval a c7308 := derived7308 a h
  have h10 : Entails.eval a c7382 := derived7382 a h
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7393 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c209, some c204, some c203, some c195, some c205, some c207, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7393 : lratChecker f7393 p7393 = .success := by decide +kernel
theorem unsat7393 : Unsatisfiable (PosFin 65) f7393 := by
  apply lratCheckerSound f7393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7393
  · intro a ha; simp [p7393] at ha; subst a; trivial
  · exact checked7393
theorem derived7393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7393 := by
  apply localUnsat_implies_entails f7393 [c7132, c209, c204, c203, c195, c205, c207] c7393 unsat7393 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7394 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7143, some c7393, some c7138, some c180, some c206, some c189, some c188, some c186, some c195, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7394 : lratChecker f7394 p7394 = .success := by decide +kernel
theorem unsat7394 : Unsatisfiable (PosFin 65) f7394 := by
  apply lratCheckerSound f7394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7394
  · intro a ha; simp [p7394] at ha; subst a; trivial
  · exact checked7394
theorem derived7394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7394 := by
  apply localUnsat_implies_entails f7394 [c7132, c7143, c7393, c7138, c180, c206, c189, c188, c186, c195] c7394 unsat7394 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c7143 := derived7143 a h
  have h2 : Entails.eval a c7393 := derived7393 a h
  have h3 : Entails.eval a c7138 := derived7138 a h
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7395 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c232, some c237, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7395 : lratChecker f7395 p7395 = .success := by decide +kernel
theorem unsat7395 : Unsatisfiable (PosFin 65) f7395 := by
  apply lratCheckerSound f7395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7395
  · intro a ha; simp [p7395] at ha; subst a; trivial
  · exact checked7395
theorem derived7395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7395 := by
  apply localUnsat_implies_entails f7395 [c232, c237] c7395 unsat7395 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7396 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c753, some c7291, some c279, some c7296, some c7341, some c267, some c261, some c749, some c268, some c7395, some c7201, some c2283, some c2279, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7396 : lratChecker f7396 p7396 = .success := by decide +kernel
theorem unsat7396 : Unsatisfiable (PosFin 65) f7396 := by
  apply lratCheckerSound f7396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7396
  · intro a ha; simp [p7396] at ha; subst a; trivial
  · exact checked7396
theorem derived7396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7396 := by
  apply localUnsat_implies_entails f7396 [c7394, c753, c7291, c279, c7296, c7341, c267, c261, c749, c268, c7395, c7201, c2283, c2279] c7396 unsat7396 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c753 := h 752 (by decide)
  have h2 : Entails.eval a c7291 := derived7291 a h
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c7296 := derived7296 a h
  have h5 : Entails.eval a c7341 := derived7341 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c749 := h 748 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c7395 := derived7395 a h
  have h11 : Entails.eval a c7201 := derived7201 a h
  have h12 : Entails.eval a c2283 := h 2282 (by decide)
  have h13 : Entails.eval a c2279 := h 2278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7397 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7291, some c249, some c271, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7397 : lratChecker f7397 p7397 = .success := by decide +kernel
theorem unsat7397 : Unsatisfiable (PosFin 65) f7397 := by
  apply lratCheckerSound f7397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7397
  · intro a ha; simp [p7397] at ha; subst a; trivial
  · exact checked7397
theorem derived7397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7397 := by
  apply localUnsat_implies_entails f7397 [c7394, c7291, c249, c271] c7397 unsat7397 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7291 := derived7291 a h
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7398 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7396, some c781, some c266, some c7397, some c7297, some c7285, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7398 : lratChecker f7398 p7398 = .success := by decide +kernel
theorem unsat7398 : Unsatisfiable (PosFin 65) f7398 := by
  apply lratCheckerSound f7398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7398
  · intro a ha; simp [p7398] at ha; subst a; trivial
  · exact checked7398
theorem derived7398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7398 := by
  apply localUnsat_implies_entails f7398 [c7394, c7396, c781, c266, c7397, c7297, c7285] c7398 unsat7398 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7396 := derived7396 a h
  have h2 : Entails.eval a c781 := h 780 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c7397 := derived7397 a h
  have h5 : Entails.eval a c7297 := derived7297 a h
  have h6 : Entails.eval a c7285 := derived7285 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7399 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1617, some c7259, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7399 : lratChecker f7399 p7399 = .success := by decide +kernel
theorem unsat7399 : Unsatisfiable (PosFin 65) f7399 := by
  apply lratCheckerSound f7399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7399
  · intro a ha; simp [p7399] at ha; subst a; trivial
  · exact checked7399
theorem derived7399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7399 := by
  apply localUnsat_implies_entails f7399 [c1617, c7259] c7399 unsat7399 (by rfl) a
  have h0 : Entails.eval a c1617 := h 1616 (by decide)
  have h1 : Entails.eval a c7259 := derived7259 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7400 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨30, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c232, some c240, some c7395, some c1361, some c1037, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7400 : lratChecker f7400 p7400 = .success := by decide +kernel
theorem unsat7400 : Unsatisfiable (PosFin 65) f7400 := by
  apply lratCheckerSound f7400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7400
  · intro a ha; simp [p7400] at ha; subst a; trivial
  · exact checked7400
theorem derived7400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7400 := by
  apply localUnsat_implies_entails f7400 [c232, c240, c7395, c1361, c1037] c7400 unsat7400 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c240 := h 239 (by decide)
  have h2 : Entails.eval a c7395 := derived7395 a h
  have h3 : Entails.eval a c1361 := h 1360 (by decide)
  have h4 : Entails.eval a c1037 := h 1036 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7401 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1416, some c1752, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7401 : lratChecker f7401 p7401 = .success := by decide +kernel
theorem unsat7401 : Unsatisfiable (PosFin 65) f7401 := by
  apply lratCheckerSound f7401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7401
  · intro a ha; simp [p7401] at ha; subst a; trivial
  · exact checked7401
theorem derived7401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7401 := by
  apply localUnsat_implies_entails f7401 [c1416, c1752] c7401 unsat7401 (by rfl) a
  have h0 : Entails.eval a c1416 := h 1415 (by decide)
  have h1 : Entails.eval a c1752 := h 1751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7402 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7287, some c7401, some c709, some c217, some c7400, some c216, some c6678, some c6679, some c102, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7402 : lratChecker f7402 p7402 = .success := by decide +kernel
theorem unsat7402 : Unsatisfiable (PosFin 65) f7402 := by
  apply lratCheckerSound f7402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7402
  · intro a ha; simp [p7402] at ha; subst a; trivial
  · exact checked7402
theorem derived7402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7402 := by
  apply localUnsat_implies_entails f7402 [c7394, c7287, c7401, c709, c217, c7400, c216, c6678, c6679, c102] c7402 unsat7402 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7287 := derived7287 a h
  have h2 : Entails.eval a c7401 := derived7401 a h
  have h3 : Entails.eval a c709 := h 708 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c7400 := derived7400 a h
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c6678 := derived6678 a h
  have h8 : Entails.eval a c6679 := derived6679 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7403 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7400, some c1418, some c1752, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7403 : lratChecker f7403 p7403 = .success := by decide +kernel
theorem unsat7403 : Unsatisfiable (PosFin 65) f7403 := by
  apply lratCheckerSound f7403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7403
  · intro a ha; simp [p7403] at ha; subst a; trivial
  · exact checked7403
theorem derived7403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7403 := by
  apply localUnsat_implies_entails f7403 [c7394, c7400, c1418, c1752] c7403 unsat7403 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7400 := derived7400 a h
  have h2 : Entails.eval a c1418 := h 1417 (by decide)
  have h3 : Entails.eval a c1752 := h 1751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7404 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1776, some c1752, some c1757, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p7404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7404 : lratChecker f7404 p7404 = .success := by decide +kernel
theorem unsat7404 : Unsatisfiable (PosFin 65) f7404 := by
  apply lratCheckerSound f7404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7404
  · intro a ha; simp [p7404] at ha; subst a; trivial
  · exact checked7404
theorem derived7404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7404 := by
  apply localUnsat_implies_entails f7404 [c1776, c1752, c1757] c7404 unsat7404 (by rfl) a
  have h0 : Entails.eval a c1776 := h 1775 (by decide)
  have h1 : Entails.eval a c1752 := h 1751 (by decide)
  have h2 : Entails.eval a c1757 := h 1756 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7405 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7399, some c7402, some c7404, some c698, some c230, some c234, some c231, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7405 : lratChecker f7405 p7405 = .success := by decide +kernel
theorem unsat7405 : Unsatisfiable (PosFin 65) f7405 := by
  apply lratCheckerSound f7405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7405
  · intro a ha; simp [p7405] at ha; subst a; trivial
  · exact checked7405
theorem derived7405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7405 := by
  apply localUnsat_implies_entails f7405 [c7394, c7399, c7402, c7404, c698, c230, c234, c231] c7405 unsat7405 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7399 := derived7399 a h
  have h2 : Entails.eval a c7402 := derived7402 a h
  have h3 : Entails.eval a c7404 := derived7404 a h
  have h4 : Entails.eval a c698 := h 697 (by decide)
  have h5 : Entails.eval a c230 := h 229 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7406 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c720, some c243, some c234, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7406 : lratChecker f7406 p7406 = .success := by decide +kernel
theorem unsat7406 : Unsatisfiable (PosFin 65) f7406 := by
  apply lratCheckerSound f7406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7406
  · intro a ha; simp [p7406] at ha; subst a; trivial
  · exact checked7406
theorem derived7406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7406 := by
  apply localUnsat_implies_entails f7406 [c720, c243, c234] c7406 unsat7406 (by rfl) a
  have h0 : Entails.eval a c720 := h 719 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7407 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7406, some c1445, some c1448, some c1775, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7407 : lratChecker f7407 p7407 = .success := by decide +kernel
theorem unsat7407 : Unsatisfiable (PosFin 65) f7407 := by
  apply lratCheckerSound f7407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7407
  · intro a ha; simp [p7407] at ha; subst a; trivial
  · exact checked7407
theorem derived7407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7407 := by
  apply localUnsat_implies_entails f7407 [c7394, c7406, c1445, c1448, c1775] c7407 unsat7407 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7406 := derived7406 a h
  have h2 : Entails.eval a c1445 := h 1444 (by decide)
  have h3 : Entails.eval a c1448 := h 1447 (by decide)
  have h4 : Entails.eval a c1775 := h 1774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7408 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c698, some c223, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7408 : lratChecker f7408 p7408 = .success := by decide +kernel
theorem unsat7408 : Unsatisfiable (PosFin 65) f7408 := by
  apply lratCheckerSound f7408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7408
  · intro a ha; simp [p7408] at ha; subst a; trivial
  · exact checked7408
theorem derived7408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7408 := by
  apply localUnsat_implies_entails f7408 [c698, c223] c7408 unsat7408 (by rfl) a
  have h0 : Entails.eval a c698 := h 697 (by decide)
  have h1 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7409 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7291, some c7408, some c1770, some c1776, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7409 : lratChecker f7409 p7409 = .success := by decide +kernel
theorem unsat7409 : Unsatisfiable (PosFin 65) f7409 := by
  apply lratCheckerSound f7409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7409
  · intro a ha; simp [p7409] at ha; subst a; trivial
  · exact checked7409
theorem derived7409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7409 := by
  apply localUnsat_implies_entails f7409 [c7394, c7291, c7408, c1770, c1776] c7409 unsat7409 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7291 := derived7291 a h
  have h2 : Entails.eval a c7408 := derived7408 a h
  have h3 : Entails.eval a c1770 := h 1769 (by decide)
  have h4 : Entails.eval a c1776 := h 1775 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7410 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7398, some c7407, some c7409, some c7405, some c7287, some c1296, some c1367, some c1918, some c7273, some c1336, some c7201, some c2072, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7410 : lratChecker f7410 p7410 = .success := by decide +kernel
theorem unsat7410 : Unsatisfiable (PosFin 65) f7410 := by
  apply lratCheckerSound f7410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7410
  · intro a ha; simp [p7410] at ha; subst a; trivial
  · exact checked7410
theorem derived7410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7410 := by
  apply localUnsat_implies_entails f7410 [c7394, c7398, c7407, c7409, c7405, c7287, c1296, c1367, c1918, c7273, c1336, c7201, c2072] c7410 unsat7410 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7398 := derived7398 a h
  have h2 : Entails.eval a c7407 := derived7407 a h
  have h3 : Entails.eval a c7409 := derived7409 a h
  have h4 : Entails.eval a c7405 := derived7405 a h
  have h5 : Entails.eval a c7287 := derived7287 a h
  have h6 : Entails.eval a c1296 := h 1295 (by decide)
  have h7 : Entails.eval a c1367 := h 1366 (by decide)
  have h8 : Entails.eval a c1918 := h 1917 (by decide)
  have h9 : Entails.eval a c7273 := derived7273 a h
  have h10 : Entails.eval a c1336 := h 1335 (by decide)
  have h11 : Entails.eval a c7201 := derived7201 a h
  have h12 : Entails.eval a c2072 := h 2071 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7411 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c232, some c7395, some c244, some c268, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7411 : lratChecker f7411 p7411 = .success := by decide +kernel
theorem unsat7411 : Unsatisfiable (PosFin 65) f7411 := by
  apply lratCheckerSound f7411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7411
  · intro a ha; simp [p7411] at ha; subst a; trivial
  · exact checked7411
theorem derived7411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7411 := by
  apply localUnsat_implies_entails f7411 [c232, c7395, c244, c268] c7411 unsat7411 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c7395 := derived7395 a h
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7412 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c276, some c283, some c268, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7412 : lratChecker f7412 p7412 = .success := by decide +kernel
theorem unsat7412 : Unsatisfiable (PosFin 65) f7412 := by
  apply lratCheckerSound f7412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7412
  · intro a ha; simp [p7412] at ha; subst a; trivial
  · exact checked7412
theorem derived7412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7412 := by
  apply localUnsat_implies_entails f7412 [c276, c283, c268] c7412 unsat7412 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7413 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1567, some c7276, some c1895, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7413 : lratChecker f7413 p7413 = .success := by decide +kernel
theorem unsat7413 : Unsatisfiable (PosFin 65) f7413 := by
  apply lratCheckerSound f7413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7413
  · intro a ha; simp [p7413] at ha; subst a; trivial
  · exact checked7413
theorem derived7413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7413 := by
  apply localUnsat_implies_entails f7413 [c1567, c7276, c1895] c7413 unsat7413 (by rfl) a
  have h0 : Entails.eval a c1567 := h 1566 (by decide)
  have h1 : Entails.eval a c7276 := derived7276 a h
  have h2 : Entails.eval a c1895 := h 1894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7414 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c253, some c282, some c267, some c7412, some c7411, some c7201, some c7413, some c1200, some c1174, some c2639, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7414 : lratChecker f7414 p7414 = .success := by decide +kernel
theorem unsat7414 : Unsatisfiable (PosFin 65) f7414 := by
  apply lratCheckerSound f7414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7414
  · intro a ha; simp [p7414] at ha; subst a; trivial
  · exact checked7414
theorem derived7414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7414 := by
  apply localUnsat_implies_entails f7414 [c7394, c253, c282, c267, c7412, c7411, c7201, c7413, c1200, c1174, c2639] c7414 unsat7414 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c282 := h 281 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c7412 := derived7412 a h
  have h5 : Entails.eval a c7411 := derived7411 a h
  have h6 : Entails.eval a c7201 := derived7201 a h
  have h7 : Entails.eval a c7413 := derived7413 a h
  have h8 : Entails.eval a c1200 := h 1199 (by decide)
  have h9 : Entails.eval a c1174 := h 1173 (by decide)
  have h10 : Entails.eval a c2639 := h 2638 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7415 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7414, some c279, some c285, some c7285, some c277, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7415 : lratChecker f7415 p7415 = .success := by decide +kernel
theorem unsat7415 : Unsatisfiable (PosFin 65) f7415 := by
  apply lratCheckerSound f7415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7415
  · intro a ha; simp [p7415] at ha; subst a; trivial
  · exact checked7415
theorem derived7415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7415 := by
  apply localUnsat_implies_entails f7415 [c7414, c279, c285, c7285, c277] c7415 unsat7415 (by rfl) a
  have h0 : Entails.eval a c7414 := derived7414 a h
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  have h3 : Entails.eval a c7285 := derived7285 a h
  have h4 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7416 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7415, some c7291, some c7397, some c265, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7416 : lratChecker f7416 p7416 = .success := by decide +kernel
theorem unsat7416 : Unsatisfiable (PosFin 65) f7416 := by
  apply lratCheckerSound f7416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7416
  · intro a ha; simp [p7416] at ha; subst a; trivial
  · exact checked7416
theorem derived7416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7416 := by
  apply localUnsat_implies_entails f7416 [c7394, c7415, c7291, c7397, c265] c7416 unsat7416 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7415 := derived7415 a h
  have h2 : Entails.eval a c7291 := derived7291 a h
  have h3 : Entails.eval a c7397 := derived7397 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7417 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c234, some c235, some c230, some c231, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p7417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7417 : lratChecker f7417 p7417 = .success := by decide +kernel
theorem unsat7417 : Unsatisfiable (PosFin 65) f7417 := by
  apply lratCheckerSound f7417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7417
  · intro a ha; simp [p7417] at ha; subst a; trivial
  · exact checked7417
theorem derived7417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7417 := by
  apply localUnsat_implies_entails f7417 [c234, c235, c230, c231] c7417 unsat7417 (by rfl) a
  have h0 : Entails.eval a c234 := h 233 (by decide)
  have h1 : Entails.eval a c235 := h 234 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7418 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7417, some c7404, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7418 : lratChecker f7418 p7418 = .success := by decide +kernel
theorem unsat7418 : Unsatisfiable (PosFin 65) f7418 := by
  apply lratCheckerSound f7418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7418
  · intro a ha; simp [p7418] at ha; subst a; trivial
  · exact checked7418
theorem derived7418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7418 := by
  apply localUnsat_implies_entails f7418 [c7394, c7417, c7404] c7418 unsat7418 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7417 := derived7417 a h
  have h2 : Entails.eval a c7404 := derived7404 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7419 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7273, some c1700, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7419 : lratChecker f7419 p7419 = .success := by decide +kernel
theorem unsat7419 : Unsatisfiable (PosFin 65) f7419 := by
  apply lratCheckerSound f7419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7419
  · intro a ha; simp [p7419] at ha; subst a; trivial
  · exact checked7419
theorem derived7419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7419 := by
  apply localUnsat_implies_entails f7419 [c7273, c1700] c7419 unsat7419 (by rfl) a
  have h0 : Entails.eval a c7273 := derived7273 a h
  have h1 : Entails.eval a c1700 := h 1699 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7420 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7418, some c7259, some c7282, some c7419, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7420 : lratChecker f7420 p7420 = .success := by decide +kernel
theorem unsat7420 : Unsatisfiable (PosFin 65) f7420 := by
  apply lratCheckerSound f7420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7420
  · intro a ha; simp [p7420] at ha; subst a; trivial
  · exact checked7420
theorem derived7420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7420 := by
  apply localUnsat_implies_entails f7420 [c7394, c7418, c7259, c7282, c7419] c7420 unsat7420 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7418 := derived7418 a h
  have h2 : Entails.eval a c7259 := derived7259 a h
  have h3 : Entails.eval a c7282 := derived7282 a h
  have h4 : Entails.eval a c7419 := derived7419 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7421 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c241, some c1778, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7421 : lratChecker f7421 p7421 = .success := by decide +kernel
theorem unsat7421 : Unsatisfiable (PosFin 65) f7421 := by
  apply lratCheckerSound f7421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7421
  · intro a ha; simp [p7421] at ha; subst a; trivial
  · exact checked7421
theorem derived7421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7421 := by
  apply localUnsat_implies_entails f7421 [c241, c1778] c7421 unsat7421 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c1778 := h 1777 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7422 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7421, some c7417, some c1775, some c1448, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7422 : lratChecker f7422 p7422 = .success := by decide +kernel
theorem unsat7422 : Unsatisfiable (PosFin 65) f7422 := by
  apply lratCheckerSound f7422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7422
  · intro a ha; simp [p7422] at ha; subst a; trivial
  · exact checked7422
theorem derived7422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7422 := by
  apply localUnsat_implies_entails f7422 [c7394, c7421, c7417, c1775, c1448] c7422 unsat7422 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7421 := derived7421 a h
  have h2 : Entails.eval a c7417 := derived7417 a h
  have h3 : Entails.eval a c1775 := h 1774 (by decide)
  have h4 : Entails.eval a c1448 := h 1447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7423 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7410, some c7416, some c7422, some c7420, some c7291, some c7417, some c1776, some c1770, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7423 : lratChecker f7423 p7423 = .success := by decide +kernel
theorem unsat7423 : Unsatisfiable (PosFin 65) f7423 := by
  apply lratCheckerSound f7423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7423
  · intro a ha; simp [p7423] at ha; subst a; trivial
  · exact checked7423
theorem derived7423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7423 := by
  apply localUnsat_implies_entails f7423 [c7394, c7410, c7416, c7422, c7420, c7291, c7417, c1776, c1770] c7423 unsat7423 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7410 := derived7410 a h
  have h2 : Entails.eval a c7416 := derived7416 a h
  have h3 : Entails.eval a c7422 := derived7422 a h
  have h4 : Entails.eval a c7420 := derived7420 a h
  have h5 : Entails.eval a c7291 := derived7291 a h
  have h6 : Entails.eval a c7417 := derived7417 a h
  have h7 : Entails.eval a c1776 := h 1775 (by decide)
  have h8 : Entails.eval a c1770 := h 1769 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7424 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c757, some c754, some c272, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7424 : lratChecker f7424 p7424 = .success := by decide +kernel
theorem unsat7424 : Unsatisfiable (PosFin 65) f7424 := by
  apply lratCheckerSound f7424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7424
  · intro a ha; simp [p7424] at ha; subst a; trivial
  · exact checked7424
theorem derived7424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7424 := by
  apply localUnsat_implies_entails f7424 [c757, c754, c272] c7424 unsat7424 (by rfl) a
  have h0 : Entails.eval a c757 := h 756 (by decide)
  have h1 : Entails.eval a c754 := h 753 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7425 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1792, some c792, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7425 : lratChecker f7425 p7425 = .success := by decide +kernel
theorem unsat7425 : Unsatisfiable (PosFin 65) f7425 := by
  apply lratCheckerSound f7425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7425
  · intro a ha; simp [p7425] at ha; subst a; trivial
  · exact checked7425
theorem derived7425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7425 := by
  apply localUnsat_implies_entails f7425 [c1792, c792] c7425 unsat7425 (by rfl) a
  have h0 : Entails.eval a c1792 := h 1791 (by decide)
  have h1 : Entails.eval a c792 := h 791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7426 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7297, some c7298, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7426 : lratChecker f7426 p7426 = .success := by decide +kernel
theorem unsat7426 : Unsatisfiable (PosFin 65) f7426 := by
  apply lratCheckerSound f7426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7426
  · intro a ha; simp [p7426] at ha; subst a; trivial
  · exact checked7426
theorem derived7426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7426 := by
  apply localUnsat_implies_entails f7426 [c7394, c7297, c7298] c7426 unsat7426 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7297 := derived7297 a h
  have h2 : Entails.eval a c7298 := derived7298 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7427 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7424, some c7425, some c7316, some c266, some c7426, some c785, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7427 : lratChecker f7427 p7427 = .success := by decide +kernel
theorem unsat7427 : Unsatisfiable (PosFin 65) f7427 := by
  apply lratCheckerSound f7427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7427
  · intro a ha; simp [p7427] at ha; subst a; trivial
  · exact checked7427
theorem derived7427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7427 := by
  apply localUnsat_implies_entails f7427 [c7394, c7424, c7425, c7316, c266, c7426, c785] c7427 unsat7427 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7424 := derived7424 a h
  have h2 : Entails.eval a c7425 := derived7425 a h
  have h3 : Entails.eval a c7316 := derived7316 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c7426 := derived7426 a h
  have h6 : Entails.eval a c785 := h 784 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7428 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c699, some c1762, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7428 : lratChecker f7428 p7428 = .success := by decide +kernel
theorem unsat7428 : Unsatisfiable (PosFin 65) f7428 := by
  apply lratCheckerSound f7428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7428
  · intro a ha; simp [p7428] at ha; subst a; trivial
  · exact checked7428
theorem derived7428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7428 := by
  apply localUnsat_implies_entails f7428 [c699, c1762] c7428 unsat7428 (by rfl) a
  have h0 : Entails.eval a c699 := h 698 (by decide)
  have h1 : Entails.eval a c1762 := h 1761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7429 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7291, some c7417, some c1776, some c1770, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7429 : lratChecker f7429 p7429 = .success := by decide +kernel
theorem unsat7429 : Unsatisfiable (PosFin 65) f7429 := by
  apply lratCheckerSound f7429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7429
  · intro a ha; simp [p7429] at ha; subst a; trivial
  · exact checked7429
theorem derived7429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7429 := by
  apply localUnsat_implies_entails f7429 [c7394, c7291, c7417, c1776, c1770] c7429 unsat7429 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7291 := derived7291 a h
  have h2 : Entails.eval a c7417 := derived7417 a h
  have h3 : Entails.eval a c1776 := h 1775 (by decide)
  have h4 : Entails.eval a c1770 := h 1769 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7430 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7423, some c7427, some c7422, some c7429, some c7420, some c7287, some c7428, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7430 : lratChecker f7430 p7430 = .success := by decide +kernel
theorem unsat7430 : Unsatisfiable (PosFin 65) f7430 := by
  apply lratCheckerSound f7430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7430
  · intro a ha; simp [p7430] at ha; subst a; trivial
  · exact checked7430
theorem derived7430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7430 := by
  apply localUnsat_implies_entails f7430 [c7394, c7423, c7427, c7422, c7429, c7420, c7287, c7428] c7430 unsat7430 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7423 := derived7423 a h
  have h2 : Entails.eval a c7427 := derived7427 a h
  have h3 : Entails.eval a c7422 := derived7422 a h
  have h4 : Entails.eval a c7429 := derived7429 a h
  have h5 : Entails.eval a c7420 := derived7420 a h
  have h6 : Entails.eval a c7287 := derived7287 a h
  have h7 : Entails.eval a c7428 := derived7428 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7431 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2283, some c1632, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7431 : lratChecker f7431 p7431 = .success := by decide +kernel
theorem unsat7431 : Unsatisfiable (PosFin 65) f7431 := by
  apply lratCheckerSound f7431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7431
  · intro a ha; simp [p7431] at ha; subst a; trivial
  · exact checked7431
theorem derived7431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7431 := by
  apply localUnsat_implies_entails f7431 [c2283, c1632] c7431 unsat7431 (by rfl) a
  have h0 : Entails.eval a c2283 := h 2282 (by decide)
  have h1 : Entails.eval a c1632 := h 1631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7432 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1314, some c1629, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7432 : lratChecker f7432 p7432 = .success := by decide +kernel
theorem unsat7432 : Unsatisfiable (PosFin 65) f7432 := by
  apply lratCheckerSound f7432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7432
  · intro a ha; simp [p7432] at ha; subst a; trivial
  · exact checked7432
theorem derived7432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7432 := by
  apply localUnsat_implies_entails f7432 [c1314, c1629] c7432 unsat7432 (by rfl) a
  have h0 : Entails.eval a c1314 := h 1313 (by decide)
  have h1 : Entails.eval a c1629 := h 1628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7433 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨8, by decide⟩, false), (⟨28, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c103, some c111, some c2239, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7433 : lratChecker f7433 p7433 = .success := by decide +kernel
theorem unsat7433 : Unsatisfiable (PosFin 65) f7433 := by
  apply lratCheckerSound f7433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7433
  · intro a ha; simp [p7433] at ha; subst a; trivial
  · exact checked7433
theorem derived7433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7433 := by
  apply localUnsat_implies_entails f7433 [c103, c111, c2239] c7433 unsat7433 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c2239 := h 2238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7434 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7392, some c7394, some c7339, some c1379, some c1729, some c7433, some c6701, some c6702, some c287, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7434 : lratChecker f7434 p7434 = .success := by decide +kernel
theorem unsat7434 : Unsatisfiable (PosFin 65) f7434 := by
  apply lratCheckerSound f7434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7434
  · intro a ha; simp [p7434] at ha; subst a; trivial
  · exact checked7434
theorem derived7434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7434 := by
  apply localUnsat_implies_entails f7434 [c7392, c7394, c7339, c1379, c1729, c7433, c6701, c6702, c287] c7434 unsat7434 (by rfl) a
  have h0 : Entails.eval a c7392 := derived7392 a h
  have h1 : Entails.eval a c7394 := derived7394 a h
  have h2 : Entails.eval a c7339 := derived7339 a h
  have h3 : Entails.eval a c1379 := h 1378 (by decide)
  have h4 : Entails.eval a c1729 := h 1728 (by decide)
  have h5 : Entails.eval a c7433 := derived7433 a h
  have h6 : Entails.eval a c6701 := derived6701 a h
  have h7 : Entails.eval a c6702 := derived6702 a h
  have h8 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7435 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c104, some c1166, some c2239, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7435 : lratChecker f7435 p7435 = .success := by decide +kernel
theorem unsat7435 : Unsatisfiable (PosFin 65) f7435 := by
  apply lratCheckerSound f7435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7435
  · intro a ha; simp [p7435] at ha; subst a; trivial
  · exact checked7435
theorem derived7435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7435 := by
  apply localUnsat_implies_entails f7435 [c104, c1166, c2239] c7435 unsat7435 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c1166 := h 1165 (by decide)
  have h2 : Entails.eval a c2239 := h 2238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7436 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7392, some c7394, some c7424, some c7430, some c755, some c748, some c768, some c775, some c266, some c258, some c7395, some c7431, some c7432, some c270, some c779, some c1675, some c1375, some c7435, some c6701, some c6702, some c287, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7436 : lratChecker f7436 p7436 = .success := by decide +kernel
theorem unsat7436 : Unsatisfiable (PosFin 65) f7436 := by
  apply lratCheckerSound f7436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7436
  · intro a ha; simp [p7436] at ha; subst a; trivial
  · exact checked7436
theorem derived7436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7436 := by
  apply localUnsat_implies_entails f7436 [c7339, c7392, c7394, c7424, c7430, c755, c748, c768, c775, c266, c258, c7395, c7431, c7432, c270, c779, c1675, c1375, c7435, c6701, c6702, c287] c7436 unsat7436 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7392 := derived7392 a h
  have h2 : Entails.eval a c7394 := derived7394 a h
  have h3 : Entails.eval a c7424 := derived7424 a h
  have h4 : Entails.eval a c7430 := derived7430 a h
  have h5 : Entails.eval a c755 := h 754 (by decide)
  have h6 : Entails.eval a c748 := h 747 (by decide)
  have h7 : Entails.eval a c768 := h 767 (by decide)
  have h8 : Entails.eval a c775 := h 774 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c7395 := derived7395 a h
  have h12 : Entails.eval a c7431 := derived7431 a h
  have h13 : Entails.eval a c7432 := derived7432 a h
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c779 := h 778 (by decide)
  have h16 : Entails.eval a c1675 := h 1674 (by decide)
  have h17 : Entails.eval a c1375 := h 1374 (by decide)
  have h18 : Entails.eval a c7435 := derived7435 a h
  have h19 : Entails.eval a c6701 := derived6701 a h
  have h20 : Entails.eval a c6702 := derived6702 a h
  have h21 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7437 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7392, some c7394, some c7424, some c7430, some c755, some c748, some c768, some c775, some c266, some c258, some c7395, some c7431, some c7432, some c270, some c779, some c253, some c254, some c7436, some c1693, some c7434, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7437 : lratChecker f7437 p7437 = .success := by decide +kernel
theorem unsat7437 : Unsatisfiable (PosFin 65) f7437 := by
  apply lratCheckerSound f7437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7437
  · intro a ha; simp [p7437] at ha; subst a; trivial
  · exact checked7437
theorem derived7437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7437 := by
  apply localUnsat_implies_entails f7437 [c7339, c7392, c7394, c7424, c7430, c755, c748, c768, c775, c266, c258, c7395, c7431, c7432, c270, c779, c253, c254, c7436, c1693, c7434] c7437 unsat7437 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7392 := derived7392 a h
  have h2 : Entails.eval a c7394 := derived7394 a h
  have h3 : Entails.eval a c7424 := derived7424 a h
  have h4 : Entails.eval a c7430 := derived7430 a h
  have h5 : Entails.eval a c755 := h 754 (by decide)
  have h6 : Entails.eval a c748 := h 747 (by decide)
  have h7 : Entails.eval a c768 := h 767 (by decide)
  have h8 : Entails.eval a c775 := h 774 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c7395 := derived7395 a h
  have h12 : Entails.eval a c7431 := derived7431 a h
  have h13 : Entails.eval a c7432 := derived7432 a h
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c779 := h 778 (by decide)
  have h16 : Entails.eval a c253 := h 252 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c7436 := derived7436 a h
  have h19 : Entails.eval a c1693 := h 1692 (by decide)
  have h20 : Entails.eval a c7434 := derived7434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7438 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7392, some c7430, some c7394, some c7424, some c748, some c755, some c768, some c775, some c266, some c258, some c7395, some c7431, some c7432, some c7437, some c2194, some c2213, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7438 : lratChecker f7438 p7438 = .success := by decide +kernel
theorem unsat7438 : Unsatisfiable (PosFin 65) f7438 := by
  apply lratCheckerSound f7438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7438
  · intro a ha; simp [p7438] at ha; subst a; trivial
  · exact checked7438
theorem derived7438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7438 := by
  apply localUnsat_implies_entails f7438 [c7339, c7392, c7430, c7394, c7424, c748, c755, c768, c775, c266, c258, c7395, c7431, c7432, c7437, c2194, c2213] c7438 unsat7438 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7392 := derived7392 a h
  have h2 : Entails.eval a c7430 := derived7430 a h
  have h3 : Entails.eval a c7394 := derived7394 a h
  have h4 : Entails.eval a c7424 := derived7424 a h
  have h5 : Entails.eval a c748 := h 747 (by decide)
  have h6 : Entails.eval a c755 := h 754 (by decide)
  have h7 : Entails.eval a c768 := h 767 (by decide)
  have h8 : Entails.eval a c775 := h 774 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c7395 := derived7395 a h
  have h12 : Entails.eval a c7431 := derived7431 a h
  have h13 : Entails.eval a c7432 := derived7432 a h
  have h14 : Entails.eval a c7437 := derived7437 a h
  have h15 : Entails.eval a c2194 := h 2193 (by decide)
  have h16 : Entails.eval a c2213 := h 2212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7439 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7373, some c1583, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p7439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7439 : lratChecker f7439 p7439 = .success := by decide +kernel
theorem unsat7439 : Unsatisfiable (PosFin 65) f7439 := by
  apply lratCheckerSound f7439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7439
  · intro a ha; simp [p7439] at ha; subst a; trivial
  · exact checked7439
theorem derived7439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7439 := by
  apply localUnsat_implies_entails f7439 [c7373, c1583] c7439 unsat7439 (by rfl) a
  have h0 : Entails.eval a c7373 := derived7373 a h
  have h1 : Entails.eval a c1583 := h 1582 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7440 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1733, some c2540, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7440 : lratChecker f7440 p7440 = .success := by decide +kernel
theorem unsat7440 : Unsatisfiable (PosFin 65) f7440 := by
  apply lratCheckerSound f7440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7440
  · intro a ha; simp [p7440] at ha; subst a; trivial
  · exact checked7440
theorem derived7440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7440 := by
  apply localUnsat_implies_entails f7440 [c1733, c2540] c7440 unsat7440 (by rfl) a
  have h0 : Entails.eval a c1733 := h 1732 (by decide)
  have h1 : Entails.eval a c2540 := h 2539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7441 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7438, some c7339, some c7392, some c7430, some c7394, some c7439, some c282, some c7316, some c272, some c266, some c787, some c801, some c270, some c7395, some c280, some c253, some c7215, some c254, some c7440, some c7432, some c7130, some c7434, some c1946, some c1675, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked7441 : lratChecker f7441 p7441 = .success := by decide +kernel
theorem unsat7441 : Unsatisfiable (PosFin 65) f7441 := by
  apply lratCheckerSound f7441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7441
  · intro a ha; simp [p7441] at ha; subst a; trivial
  · exact checked7441
theorem derived7441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7441 := by
  apply localUnsat_implies_entails f7441 [c7438, c7339, c7392, c7430, c7394, c7439, c282, c7316, c272, c266, c787, c801, c270, c7395, c280, c253, c7215, c254, c7440, c7432, c7130, c7434, c1946, c1675] c7441 unsat7441 (by rfl) a
  have h0 : Entails.eval a c7438 := derived7438 a h
  have h1 : Entails.eval a c7339 := derived7339 a h
  have h2 : Entails.eval a c7392 := derived7392 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7394 := derived7394 a h
  have h5 : Entails.eval a c7439 := derived7439 a h
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c7316 := derived7316 a h
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c787 := h 786 (by decide)
  have h11 : Entails.eval a c801 := h 800 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c7395 := derived7395 a h
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c253 := h 252 (by decide)
  have h16 : Entails.eval a c7215 := derived7215 a h
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c7440 := derived7440 a h
  have h19 : Entails.eval a c7432 := derived7432 a h
  have h20 : Entails.eval a c7130 := derived7130 a h
  have h21 : Entails.eval a c7434 := derived7434 a h
  have h22 : Entails.eval a c1946 := h 1945 (by decide)
  have h23 : Entails.eval a c1675 := h 1674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7442 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7392, some c7394, some c7438, some c7441, some c7425, some c7316, some c272, some c794, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7442 : lratChecker f7442 p7442 = .success := by decide +kernel
theorem unsat7442 : Unsatisfiable (PosFin 65) f7442 := by
  apply lratCheckerSound f7442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7442
  · intro a ha; simp [p7442] at ha; subst a; trivial
  · exact checked7442
theorem derived7442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7442 := by
  apply localUnsat_implies_entails f7442 [c7392, c7394, c7438, c7441, c7425, c7316, c272, c794] c7442 unsat7442 (by rfl) a
  have h0 : Entails.eval a c7392 := derived7392 a h
  have h1 : Entails.eval a c7394 := derived7394 a h
  have h2 : Entails.eval a c7438 := derived7438 a h
  have h3 : Entails.eval a c7441 := derived7441 a h
  have h4 : Entails.eval a c7425 := derived7425 a h
  have h5 : Entails.eval a c7316 := derived7316 a h
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c794 := h 793 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7443 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1296, some c1721, some c1918, some c1662, some c1336, some c154, some c161, some c3390, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7443 : lratChecker f7443 p7443 = .success := by decide +kernel
theorem unsat7443 : Unsatisfiable (PosFin 65) f7443 := by
  apply lratCheckerSound f7443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7443
  · intro a ha; simp [p7443] at ha; subst a; trivial
  · exact checked7443
theorem derived7443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7443 := by
  apply localUnsat_implies_entails f7443 [c1296, c1721, c1918, c1662, c1336, c154, c161, c3390] c7443 unsat7443 (by rfl) a
  have h0 : Entails.eval a c1296 := h 1295 (by decide)
  have h1 : Entails.eval a c1721 := h 1720 (by decide)
  have h2 : Entails.eval a c1918 := h 1917 (by decide)
  have h3 : Entails.eval a c1662 := h 1661 (by decide)
  have h4 : Entails.eval a c1336 := h 1335 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c3390 := h 3389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7444 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c695, some c701, some c7417, some c228, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7444 : lratChecker f7444 p7444 = .success := by decide +kernel
theorem unsat7444 : Unsatisfiable (PosFin 65) f7444 := by
  apply lratCheckerSound f7444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7444
  · intro a ha; simp [p7444] at ha; subst a; trivial
  · exact checked7444
theorem derived7444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7444 := by
  apply localUnsat_implies_entails f7444 [c695, c701, c7417, c228] c7444 unsat7444 (by rfl) a
  have h0 : Entails.eval a c695 := h 694 (by decide)
  have h1 : Entails.eval a c701 := h 700 (by decide)
  have h2 : Entails.eval a c7417 := derived7417 a h
  have h3 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7445 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1431, some c1433, some c1775, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7445 : lratChecker f7445 p7445 = .success := by decide +kernel
theorem unsat7445 : Unsatisfiable (PosFin 65) f7445 := by
  apply lratCheckerSound f7445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7445
  · intro a ha; simp [p7445] at ha; subst a; trivial
  · exact checked7445
theorem derived7445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7445 := by
  apply localUnsat_implies_entails f7445 [c1431, c1433, c1775] c7445 unsat7445 (by rfl) a
  have h0 : Entails.eval a c1431 := h 1430 (by decide)
  have h1 : Entails.eval a c1433 := h 1432 (by decide)
  have h2 : Entails.eval a c1775 := h 1774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7446 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨28, by decide⟩, false), (⟨11, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c103, some c111, some c3349, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7446 : lratChecker f7446 p7446 = .success := by decide +kernel
theorem unsat7446 : Unsatisfiable (PosFin 65) f7446 := by
  apply lratCheckerSound f7446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7446
  · intro a ha; simp [p7446] at ha; subst a; trivial
  · exact checked7446
theorem derived7446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7446 := by
  apply localUnsat_implies_entails f7446 [c103, c111, c3349] c7446 unsat7446 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c3349 := h 3348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7447 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7392, some c7339, some c1379, some c7446, some c6671, some c6672, some c20, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7447 : lratChecker f7447 p7447 = .success := by decide +kernel
theorem unsat7447 : Unsatisfiable (PosFin 65) f7447 := by
  apply lratCheckerSound f7447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7447
  · intro a ha; simp [p7447] at ha; subst a; trivial
  · exact checked7447
theorem derived7447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7447 := by
  apply localUnsat_implies_entails f7447 [c7392, c7339, c1379, c7446, c6671, c6672, c20] c7447 unsat7447 (by rfl) a
  have h0 : Entails.eval a c7392 := derived7392 a h
  have h1 : Entails.eval a c7339 := derived7339 a h
  have h2 : Entails.eval a c1379 := h 1378 (by decide)
  have h3 : Entails.eval a c7446 := derived7446 a h
  have h4 : Entails.eval a c6671 := derived6671 a h
  have h5 : Entails.eval a c6672 := derived6672 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7448 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c104, some c2127, some c3227, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7448 : lratChecker f7448 p7448 = .success := by decide +kernel
theorem unsat7448 : Unsatisfiable (PosFin 65) f7448 := by
  apply lratCheckerSound f7448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7448
  · intro a ha; simp [p7448] at ha; subst a; trivial
  · exact checked7448
theorem derived7448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7448 := by
  apply localUnsat_implies_entails f7448 [c104, c2127, c3227] c7448 unsat7448 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c2127 := h 2126 (by decide)
  have h2 : Entails.eval a c3227 := h 3226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7449 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7392, some c7394, some c7430, some c7442, some c7370, some c7443, some c7444, some c1779, some c1771, some c1753, some c7432, some c1419, some c7445, some c1767, some c1764, some c1440, some c1429, some c7447, some c2330, some c1675, some c1375, some c1945, some c7448, some c6671, some c6672, some c20, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked7449 : lratChecker f7449 p7449 = .success := by decide +kernel
theorem unsat7449 : Unsatisfiable (PosFin 65) f7449 := by
  apply lratCheckerSound f7449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7449
  · intro a ha; simp [p7449] at ha; subst a; trivial
  · exact checked7449
theorem derived7449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7449 := by
  apply localUnsat_implies_entails f7449 [c7339, c7392, c7394, c7430, c7442, c7370, c7443, c7444, c1779, c1771, c1753, c7432, c1419, c7445, c1767, c1764, c1440, c1429, c7447, c2330, c1675, c1375, c1945, c7448, c6671, c6672, c20] c7449 unsat7449 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7392 := derived7392 a h
  have h2 : Entails.eval a c7394 := derived7394 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7442 := derived7442 a h
  have h5 : Entails.eval a c7370 := derived7370 a h
  have h6 : Entails.eval a c7443 := derived7443 a h
  have h7 : Entails.eval a c7444 := derived7444 a h
  have h8 : Entails.eval a c1779 := h 1778 (by decide)
  have h9 : Entails.eval a c1771 := h 1770 (by decide)
  have h10 : Entails.eval a c1753 := h 1752 (by decide)
  have h11 : Entails.eval a c7432 := derived7432 a h
  have h12 : Entails.eval a c1419 := h 1418 (by decide)
  have h13 : Entails.eval a c7445 := derived7445 a h
  have h14 : Entails.eval a c1767 := h 1766 (by decide)
  have h15 : Entails.eval a c1764 := h 1763 (by decide)
  have h16 : Entails.eval a c1440 := h 1439 (by decide)
  have h17 : Entails.eval a c1429 := h 1428 (by decide)
  have h18 : Entails.eval a c7447 := derived7447 a h
  have h19 : Entails.eval a c2330 := h 2329 (by decide)
  have h20 : Entails.eval a c1675 := h 1674 (by decide)
  have h21 : Entails.eval a c1375 := h 1374 (by decide)
  have h22 : Entails.eval a c1945 := h 1944 (by decide)
  have h23 : Entails.eval a c7448 := derived7448 a h
  have h24 : Entails.eval a c6671 := derived6671 a h
  have h25 : Entails.eval a c6672 := derived6672 a h
  have h26 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7450 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2194, some c2213, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7450 : lratChecker f7450 p7450 = .success := by decide +kernel
theorem unsat7450 : Unsatisfiable (PosFin 65) f7450 := by
  apply lratCheckerSound f7450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7450
  · intro a ha; simp [p7450] at ha; subst a; trivial
  · exact checked7450
theorem derived7450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7450 := by
  apply localUnsat_implies_entails f7450 [c2194, c2213] c7450 unsat7450 (by rfl) a
  have h0 : Entails.eval a c2194 := h 2193 (by decide)
  have h1 : Entails.eval a c2213 := h 2212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7451 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7442, some c7339, some c7392, some c7430, some c7394, some c7370, some c7443, some c7444, some c1419, some c1771, some c1779, some c1753, some c1429, some c7432, some c7450, some c7449, some c1682, some c1698, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7451 : lratChecker f7451 p7451 = .success := by decide +kernel
theorem unsat7451 : Unsatisfiable (PosFin 65) f7451 := by
  apply lratCheckerSound f7451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7451
  · intro a ha; simp [p7451] at ha; subst a; trivial
  · exact checked7451
theorem derived7451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7451 := by
  apply localUnsat_implies_entails f7451 [c7442, c7339, c7392, c7430, c7394, c7370, c7443, c7444, c1419, c1771, c1779, c1753, c1429, c7432, c7450, c7449, c1682, c1698] c7451 unsat7451 (by rfl) a
  have h0 : Entails.eval a c7442 := derived7442 a h
  have h1 : Entails.eval a c7339 := derived7339 a h
  have h2 : Entails.eval a c7392 := derived7392 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7394 := derived7394 a h
  have h5 : Entails.eval a c7370 := derived7370 a h
  have h6 : Entails.eval a c7443 := derived7443 a h
  have h7 : Entails.eval a c7444 := derived7444 a h
  have h8 : Entails.eval a c1419 := h 1418 (by decide)
  have h9 : Entails.eval a c1771 := h 1770 (by decide)
  have h10 : Entails.eval a c1779 := h 1778 (by decide)
  have h11 : Entails.eval a c1753 := h 1752 (by decide)
  have h12 : Entails.eval a c1429 := h 1428 (by decide)
  have h13 : Entails.eval a c7432 := derived7432 a h
  have h14 : Entails.eval a c7450 := derived7450 a h
  have h15 : Entails.eval a c7449 := derived7449 a h
  have h16 : Entails.eval a c1682 := h 1681 (by decide)
  have h17 : Entails.eval a c1698 := h 1697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7452 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c702, some c236, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7452 : lratChecker f7452 p7452 = .success := by decide +kernel
theorem unsat7452 : Unsatisfiable (PosFin 65) f7452 := by
  apply lratCheckerSound f7452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7452
  · intro a ha; simp [p7452] at ha; subst a; trivial
  · exact checked7452
theorem derived7452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7452 := by
  apply localUnsat_implies_entails f7452 [c702, c236] c7452 unsat7452 (by rfl) a
  have h0 : Entails.eval a c702 := h 701 (by decide)
  have h1 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7453 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7442, some c7339, some c7392, some c7430, some c7394, some c7451, some c7428, some c7452, some c1428, some c1779, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7453 : lratChecker f7453 p7453 = .success := by decide +kernel
theorem unsat7453 : Unsatisfiable (PosFin 65) f7453 := by
  apply lratCheckerSound f7453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7453
  · intro a ha; simp [p7453] at ha; subst a; trivial
  · exact checked7453
theorem derived7453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7453 := by
  apply localUnsat_implies_entails f7453 [c7442, c7339, c7392, c7430, c7394, c7451, c7428, c7452, c1428, c1779] c7453 unsat7453 (by rfl) a
  have h0 : Entails.eval a c7442 := derived7442 a h
  have h1 : Entails.eval a c7339 := derived7339 a h
  have h2 : Entails.eval a c7392 := derived7392 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7394 := derived7394 a h
  have h5 : Entails.eval a c7451 := derived7451 a h
  have h6 : Entails.eval a c7428 := derived7428 a h
  have h7 : Entails.eval a c7452 := derived7452 a h
  have h8 : Entails.eval a c1428 := h 1427 (by decide)
  have h9 : Entails.eval a c1779 := h 1778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7454 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7316, some c7439, some c7417, some c242, some c727, some c2066, some c1605, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7454 : lratChecker f7454 p7454 = .success := by decide +kernel
theorem unsat7454 : Unsatisfiable (PosFin 65) f7454 := by
  apply lratCheckerSound f7454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7454
  · intro a ha; simp [p7454] at ha; subst a; trivial
  · exact checked7454
theorem derived7454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7454 := by
  apply localUnsat_implies_entails f7454 [c7394, c7316, c7439, c7417, c242, c727, c2066, c1605] c7454 unsat7454 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7316 := derived7316 a h
  have h2 : Entails.eval a c7439 := derived7439 a h
  have h3 : Entails.eval a c7417 := derived7417 a h
  have h4 : Entails.eval a c242 := h 241 (by decide)
  have h5 : Entails.eval a c727 := h 726 (by decide)
  have h6 : Entails.eval a c2066 := h 2065 (by decide)
  have h7 : Entails.eval a c1605 := h 1604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7455 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1741, some c1958, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7455 : lratChecker f7455 p7455 = .success := by decide +kernel
theorem unsat7455 : Unsatisfiable (PosFin 65) f7455 := by
  apply lratCheckerSound f7455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7455
  · intro a ha; simp [p7455] at ha; subst a; trivial
  · exact checked7455
theorem derived7455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7455 := by
  apply localUnsat_implies_entails f7455 [c1741, c1958] c7455 unsat7455 (by rfl) a
  have h0 : Entails.eval a c1741 := h 1740 (by decide)
  have h1 : Entails.eval a c1958 := h 1957 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7456 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7453, some c7442, some c7339, some c7392, some c7430, some c7394, some c7439, some c7443, some c7454, some c1419, some c1779, some c1771, some c7445, some c1758, some c7403, some c7432, some c7215, some c1764, some c7455, some c1750, some c1946, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7456 : lratChecker f7456 p7456 = .success := by decide +kernel
theorem unsat7456 : Unsatisfiable (PosFin 65) f7456 := by
  apply lratCheckerSound f7456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7456
  · intro a ha; simp [p7456] at ha; subst a; trivial
  · exact checked7456
theorem derived7456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7456 := by
  apply localUnsat_implies_entails f7456 [c7453, c7442, c7339, c7392, c7430, c7394, c7439, c7443, c7454, c1419, c1779, c1771, c7445, c1758, c7403, c7432, c7215, c1764, c7455, c1750, c1946] c7456 unsat7456 (by rfl) a
  have h0 : Entails.eval a c7453 := derived7453 a h
  have h1 : Entails.eval a c7442 := derived7442 a h
  have h2 : Entails.eval a c7339 := derived7339 a h
  have h3 : Entails.eval a c7392 := derived7392 a h
  have h4 : Entails.eval a c7430 := derived7430 a h
  have h5 : Entails.eval a c7394 := derived7394 a h
  have h6 : Entails.eval a c7439 := derived7439 a h
  have h7 : Entails.eval a c7443 := derived7443 a h
  have h8 : Entails.eval a c7454 := derived7454 a h
  have h9 : Entails.eval a c1419 := h 1418 (by decide)
  have h10 : Entails.eval a c1779 := h 1778 (by decide)
  have h11 : Entails.eval a c1771 := h 1770 (by decide)
  have h12 : Entails.eval a c7445 := derived7445 a h
  have h13 : Entails.eval a c1758 := h 1757 (by decide)
  have h14 : Entails.eval a c7403 := derived7403 a h
  have h15 : Entails.eval a c7432 := derived7432 a h
  have h16 : Entails.eval a c7215 := derived7215 a h
  have h17 : Entails.eval a c1764 := h 1763 (by decide)
  have h18 : Entails.eval a c7455 := derived7455 a h
  have h19 : Entails.eval a c1750 := h 1749 (by decide)
  have h20 : Entails.eval a c1946 := h 1945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7457 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1792, some c1762, some c730, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7457 : lratChecker f7457 p7457 = .success := by decide +kernel
theorem unsat7457 : Unsatisfiable (PosFin 65) f7457 := by
  apply lratCheckerSound f7457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7457
  · intro a ha; simp [p7457] at ha; subst a; trivial
  · exact checked7457
theorem derived7457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7457 := by
  apply localUnsat_implies_entails f7457 [c1792, c1762, c730] c7457 unsat7457 (by rfl) a
  have h0 : Entails.eval a c1792 := h 1791 (by decide)
  have h1 : Entails.eval a c1762 := h 1761 (by decide)
  have h2 : Entails.eval a c730 := h 729 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7458 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c236, some c731, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7458 : lratChecker f7458 p7458 = .success := by decide +kernel
theorem unsat7458 : Unsatisfiable (PosFin 65) f7458 := by
  apply lratCheckerSound f7458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7458
  · intro a ha; simp [p7458] at ha; subst a; trivial
  · exact checked7458
theorem derived7458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7458 := by
  apply localUnsat_implies_entails f7458 [c236, c731] c7458 unsat7458 (by rfl) a
  have h0 : Entails.eval a c236 := h 235 (by decide)
  have h1 : Entails.eval a c731 := h 730 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7459 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7392, some c7394, some c7339, some c7430, some c7442, some c7453, some c7456, some c7457, some c7316, some c7458, some c1428, some c1779, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7459 : lratChecker f7459 p7459 = .success := by decide +kernel
theorem unsat7459 : Unsatisfiable (PosFin 65) f7459 := by
  apply lratCheckerSound f7459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7459
  · intro a ha; simp [p7459] at ha; subst a; trivial
  · exact checked7459
theorem derived7459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7459 := by
  apply localUnsat_implies_entails f7459 [c7392, c7394, c7339, c7430, c7442, c7453, c7456, c7457, c7316, c7458, c1428, c1779] c7459 unsat7459 (by rfl) a
  have h0 : Entails.eval a c7392 := derived7392 a h
  have h1 : Entails.eval a c7394 := derived7394 a h
  have h2 : Entails.eval a c7339 := derived7339 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7442 := derived7442 a h
  have h5 : Entails.eval a c7453 := derived7453 a h
  have h6 : Entails.eval a c7456 := derived7456 a h
  have h7 : Entails.eval a c7457 := derived7457 a h
  have h8 : Entails.eval a c7316 := derived7316 a h
  have h9 : Entails.eval a c7458 := derived7458 a h
  have h10 : Entails.eval a c1428 := h 1427 (by decide)
  have h11 : Entails.eval a c1779 := h 1778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7460 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7310, some c7307, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7460 : lratChecker f7460 p7460 = .success := by decide +kernel
theorem unsat7460 : Unsatisfiable (PosFin 65) f7460 := by
  apply lratCheckerSound f7460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7460
  · intro a ha; simp [p7460] at ha; subst a; trivial
  · exact checked7460
theorem derived7460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7460 := by
  apply localUnsat_implies_entails f7460 [c7310, c7307] c7460 unsat7460 (by rfl) a
  have h0 : Entails.eval a c7310 := derived7310 a h
  have h1 : Entails.eval a c7307 := derived7307 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7461 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7460, some c7291, some c257, some c281, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7461 : lratChecker f7461 p7461 = .success := by decide +kernel
theorem unsat7461 : Unsatisfiable (PosFin 65) f7461 := by
  apply lratCheckerSound f7461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7461
  · intro a ha; simp [p7461] at ha; subst a; trivial
  · exact checked7461
theorem derived7461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7461 := by
  apply localUnsat_implies_entails f7461 [c7394, c7460, c7291, c257, c281] c7461 unsat7461 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7460 := derived7460 a h
  have h2 : Entails.eval a c7291 := derived7291 a h
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7462 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7461, some c264, some c269, some c258, some c274, some c255, some c278, some c779, some c286, some c249, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7462 : lratChecker f7462 p7462 = .success := by decide +kernel
theorem unsat7462 : Unsatisfiable (PosFin 65) f7462 := by
  apply lratCheckerSound f7462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7462
  · intro a ha; simp [p7462] at ha; subst a; trivial
  · exact checked7462
theorem derived7462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7462 := by
  apply localUnsat_implies_entails f7462 [c7461, c264, c269, c258, c274, c255, c278, c779, c286, c249] c7462 unsat7462 (by rfl) a
  have h0 : Entails.eval a c7461 := derived7461 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c779 := h 778 (by decide)
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7463 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7422, some c7429, some c7323, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7463 : lratChecker f7463 p7463 = .success := by decide +kernel
theorem unsat7463 : Unsatisfiable (PosFin 65) f7463 := by
  apply lratCheckerSound f7463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7463
  · intro a ha; simp [p7463] at ha; subst a; trivial
  · exact checked7463
theorem derived7463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7463 := by
  apply localUnsat_implies_entails f7463 [c7394, c7422, c7429, c7323] c7463 unsat7463 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7422 := derived7422 a h
  have h2 : Entails.eval a c7429 := derived7429 a h
  have h3 : Entails.eval a c7323 := derived7323 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7464 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7462, some c7463, some c7394, some c7444, some c1419, some c7382, some c1774, some c7445, some c1764, some c1780, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7464 : lratChecker f7464 p7464 = .success := by decide +kernel
theorem unsat7464 : Unsatisfiable (PosFin 65) f7464 := by
  apply lratCheckerSound f7464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7464
  · intro a ha; simp [p7464] at ha; subst a; trivial
  · exact checked7464
theorem derived7464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7464 := by
  apply localUnsat_implies_entails f7464 [c7462, c7463, c7394, c7444, c1419, c7382, c1774, c7445, c1764, c1780] c7464 unsat7464 (by rfl) a
  have h0 : Entails.eval a c7462 := derived7462 a h
  have h1 : Entails.eval a c7463 := derived7463 a h
  have h2 : Entails.eval a c7394 := derived7394 a h
  have h3 : Entails.eval a c7444 := derived7444 a h
  have h4 : Entails.eval a c1419 := h 1418 (by decide)
  have h5 : Entails.eval a c7382 := derived7382 a h
  have h6 : Entails.eval a c1774 := h 1773 (by decide)
  have h7 : Entails.eval a c7445 := derived7445 a h
  have h8 : Entails.eval a c1764 := h 1763 (by decide)
  have h9 : Entails.eval a c1780 := h 1779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7465 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7417, some c229, some c709, some c228, some c716, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7465 : lratChecker f7465 p7465 = .success := by decide +kernel
theorem unsat7465 : Unsatisfiable (PosFin 65) f7465 := by
  apply lratCheckerSound f7465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7465
  · intro a ha; simp [p7465] at ha; subst a; trivial
  · exact checked7465
theorem derived7465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7465 := by
  apply localUnsat_implies_entails f7465 [c7417, c229, c709, c228, c716] c7465 unsat7465 (by rfl) a
  have h0 : Entails.eval a c7417 := derived7417 a h
  have h1 : Entails.eval a c229 := h 228 (by decide)
  have h2 : Entails.eval a c709 := h 708 (by decide)
  have h3 : Entails.eval a c228 := h 227 (by decide)
  have h4 : Entails.eval a c716 := h 715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7466 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c7462, some c7463, some c7464, some c7465, some c7382, some c1774, some c1759, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7466 : lratChecker f7466 p7466 = .success := by decide +kernel
theorem unsat7466 : Unsatisfiable (PosFin 65) f7466 := by
  apply lratCheckerSound f7466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7466
  · intro a ha; simp [p7466] at ha; subst a; trivial
  · exact checked7466
theorem derived7466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7466 := by
  apply localUnsat_implies_entails f7466 [c7394, c7462, c7463, c7464, c7465, c7382, c1774, c1759] c7466 unsat7466 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c7462 := derived7462 a h
  have h2 : Entails.eval a c7463 := derived7463 a h
  have h3 : Entails.eval a c7464 := derived7464 a h
  have h4 : Entails.eval a c7465 := derived7465 a h
  have h5 : Entails.eval a c7382 := derived7382 a h
  have h6 : Entails.eval a c1774 := h 1773 (by decide)
  have h7 : Entails.eval a c1759 := h 1758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7467 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c264, some c269, some c258, some c255, some c278, some c249, some c262, some c286, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7467 : lratChecker f7467 p7467 = .success := by decide +kernel
theorem unsat7467 : Unsatisfiable (PosFin 65) f7467 := by
  apply lratCheckerSound f7467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7467
  · intro a ha; simp [p7467] at ha; subst a; trivial
  · exact checked7467
theorem derived7467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7467 := by
  apply localUnsat_implies_entails f7467 [c264, c269, c258, c255, c278, c249, c262, c286] c7467 unsat7467 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c258 := h 257 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c278 := h 277 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7468 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7461, some c7467, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7468 : lratChecker f7468 p7468 = .success := by decide +kernel
theorem unsat7468 : Unsatisfiable (PosFin 65) f7468 := by
  apply lratCheckerSound f7468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7468
  · intro a ha; simp [p7468] at ha; subst a; trivial
  · exact checked7468
theorem derived7468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7468 := by
  apply localUnsat_implies_entails f7468 [c7461, c7467] c7468 unsat7468 (by rfl) a
  have h0 : Entails.eval a c7461 := derived7461 a h
  have h1 : Entails.eval a c7467 := derived7467 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7469 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7468, some c7463, some c229, some c233, some c224, some c7400, some c238, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7469 : lratChecker f7469 p7469 = .success := by decide +kernel
theorem unsat7469 : Unsatisfiable (PosFin 65) f7469 := by
  apply lratCheckerSound f7469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7469
  · intro a ha; simp [p7469] at ha; subst a; trivial
  · exact checked7469
theorem derived7469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7469 := by
  apply localUnsat_implies_entails f7469 [c7468, c7463, c229, c233, c224, c7400, c238] c7469 unsat7469 (by rfl) a
  have h0 : Entails.eval a c7468 := derived7468 a h
  have h1 : Entails.eval a c7463 := derived7463 a h
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c7400 := derived7400 a h
  have h6 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7470 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7392, some c7394, some c7459, some c7468, some c7463, some c7469, some c7382, some c1774, some c1764, some c1780, some c1434, some c7445, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7470 : lratChecker f7470 p7470 = .success := by decide +kernel
theorem unsat7470 : Unsatisfiable (PosFin 65) f7470 := by
  apply lratCheckerSound f7470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7470
  · intro a ha; simp [p7470] at ha; subst a; trivial
  · exact checked7470
theorem derived7470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7470 := by
  apply localUnsat_implies_entails f7470 [c7339, c7392, c7394, c7459, c7468, c7463, c7469, c7382, c1774, c1764, c1780, c1434, c7445] c7470 unsat7470 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7392 := derived7392 a h
  have h2 : Entails.eval a c7394 := derived7394 a h
  have h3 : Entails.eval a c7459 := derived7459 a h
  have h4 : Entails.eval a c7468 := derived7468 a h
  have h5 : Entails.eval a c7463 := derived7463 a h
  have h6 : Entails.eval a c7469 := derived7469 a h
  have h7 : Entails.eval a c7382 := derived7382 a h
  have h8 : Entails.eval a c1774 := h 1773 (by decide)
  have h9 : Entails.eval a c1764 := h 1763 (by decide)
  have h10 : Entails.eval a c1780 := h 1779 (by decide)
  have h11 : Entails.eval a c1434 := h 1433 (by decide)
  have h12 : Entails.eval a c7445 := derived7445 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7471 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1243, some c2059, some c987, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7471 : lratChecker f7471 p7471 = .success := by decide +kernel
theorem unsat7471 : Unsatisfiable (PosFin 65) f7471 := by
  apply lratCheckerSound f7471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7471
  · intro a ha; simp [p7471] at ha; subst a; trivial
  · exact checked7471
theorem derived7471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7471 := by
  apply localUnsat_implies_entails f7471 [c1243, c2059, c987] c7471 unsat7471 (by rfl) a
  have h0 : Entails.eval a c1243 := h 1242 (by decide)
  have h1 : Entails.eval a c2059 := h 2058 (by decide)
  have h2 : Entails.eval a c987 := h 986 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7472 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨28, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7471, some c1241, some c2056, some c991, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7472 : lratChecker f7472 p7472 = .success := by decide +kernel
theorem unsat7472 : Unsatisfiable (PosFin 65) f7472 := by
  apply lratCheckerSound f7472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7472
  · intro a ha; simp [p7472] at ha; subst a; trivial
  · exact checked7472
theorem derived7472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7472 := by
  apply localUnsat_implies_entails f7472 [c7471, c1241, c2056, c991] c7472 unsat7472 (by rfl) a
  have h0 : Entails.eval a c7471 := derived7471 a h
  have h1 : Entails.eval a c1241 := h 1240 (by decide)
  have h2 : Entails.eval a c2056 := h 2055 (by decide)
  have h3 : Entails.eval a c991 := h 990 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7473 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1243, some c2407, some c2460, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7473 : lratChecker f7473 p7473 = .success := by decide +kernel
theorem unsat7473 : Unsatisfiable (PosFin 65) f7473 := by
  apply lratCheckerSound f7473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7473
  · intro a ha; simp [p7473] at ha; subst a; trivial
  · exact checked7473
theorem derived7473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7473 := by
  apply localUnsat_implies_entails f7473 [c1243, c2407, c2460] c7473 unsat7473 (by rfl) a
  have h0 : Entails.eval a c1243 := h 1242 (by decide)
  have h1 : Entails.eval a c2407 := h 2406 (by decide)
  have h2 : Entails.eval a c2460 := h 2459 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7474 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨28, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨31, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c322, some c7472, some c7473, some c1147, some c1241, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7474 : lratChecker f7474 p7474 = .success := by decide +kernel
theorem unsat7474 : Unsatisfiable (PosFin 65) f7474 := by
  apply lratCheckerSound f7474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7474
  · intro a ha; simp [p7474] at ha; subst a; trivial
  · exact checked7474
theorem derived7474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7474 := by
  apply localUnsat_implies_entails f7474 [c322, c7472, c7473, c1147, c1241] c7474 unsat7474 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c7472 := derived7472 a h
  have h2 : Entails.eval a c7473 := derived7473 a h
  have h3 : Entails.eval a c1147 := h 1146 (by decide)
  have h4 : Entails.eval a c1241 := h 1240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7475 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c905, some c2280, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7475 : lratChecker f7475 p7475 = .success := by decide +kernel
theorem unsat7475 : Unsatisfiable (PosFin 65) f7475 := by
  apply lratCheckerSound f7475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7475
  · intro a ha; simp [p7475] at ha; subst a; trivial
  · exact checked7475
theorem derived7475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7475 := by
  apply localUnsat_implies_entails f7475 [c905, c2280] c7475 unsat7475 (by rfl) a
  have h0 : Entails.eval a c905 := h 904 (by decide)
  have h1 : Entails.eval a c2280 := h 2279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7476 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c752, some c776, some c753, some c761, some c777, some c763, some c767, some c749, some c758, some c772, some c724, some c7474, some c7475, some c2283, some c1327, some c2582, some c1835, some c1219, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7476 : lratChecker f7476 p7476 = .success := by decide +kernel
theorem unsat7476 : Unsatisfiable (PosFin 65) f7476 := by
  apply lratCheckerSound f7476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7476
  · intro a ha; simp [p7476] at ha; subst a; trivial
  · exact checked7476
theorem derived7476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7476 := by
  apply localUnsat_implies_entails f7476 [c752, c776, c753, c761, c777, c763, c767, c749, c758, c772, c724, c7474, c7475, c2283, c1327, c2582, c1835, c1219] c7476 unsat7476 (by rfl) a
  have h0 : Entails.eval a c752 := h 751 (by decide)
  have h1 : Entails.eval a c776 := h 775 (by decide)
  have h2 : Entails.eval a c753 := h 752 (by decide)
  have h3 : Entails.eval a c761 := h 760 (by decide)
  have h4 : Entails.eval a c777 := h 776 (by decide)
  have h5 : Entails.eval a c763 := h 762 (by decide)
  have h6 : Entails.eval a c767 := h 766 (by decide)
  have h7 : Entails.eval a c749 := h 748 (by decide)
  have h8 : Entails.eval a c758 := h 757 (by decide)
  have h9 : Entails.eval a c772 := h 771 (by decide)
  have h10 : Entails.eval a c724 := h 723 (by decide)
  have h11 : Entails.eval a c7474 := derived7474 a h
  have h12 : Entails.eval a c7475 := derived7475 a h
  have h13 : Entails.eval a c2283 := h 2282 (by decide)
  have h14 : Entails.eval a c1327 := h 1326 (by decide)
  have h15 : Entails.eval a c2582 := h 2581 (by decide)
  have h16 : Entails.eval a c1835 := h 1834 (by decide)
  have h17 : Entails.eval a c1219 := h 1218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7477 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, true), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7170, some c2283, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7477 : lratChecker f7477 p7477 = .success := by decide +kernel
theorem unsat7477 : Unsatisfiable (PosFin 65) f7477 := by
  apply lratCheckerSound f7477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7477
  · intro a ha; simp [p7477] at ha; subst a; trivial
  · exact checked7477
theorem derived7477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7477 := by
  apply localUnsat_implies_entails f7477 [c7170, c2283] c7477 unsat7477 (by rfl) a
  have h0 : Entails.eval a c7170 := derived7170 a h
  have h1 : Entails.eval a c2283 := h 2282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7478 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7477, some c1254, some c2280, some c2270, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7478 : lratChecker f7478 p7478 = .success := by decide +kernel
theorem unsat7478 : Unsatisfiable (PosFin 65) f7478 := by
  apply lratCheckerSound f7478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7478
  · intro a ha; simp [p7478] at ha; subst a; trivial
  · exact checked7478
theorem derived7478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7478 := by
  apply localUnsat_implies_entails f7478 [c7477, c1254, c2280, c2270] c7478 unsat7478 (by rfl) a
  have h0 : Entails.eval a c7477 := derived7477 a h
  have h1 : Entails.eval a c1254 := h 1253 (by decide)
  have h2 : Entails.eval a c2280 := h 2279 (by decide)
  have h3 : Entails.eval a c2270 := h 2269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7479 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨30, by decide⟩, true), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2283, some c1305, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7479 : lratChecker f7479 p7479 = .success := by decide +kernel
theorem unsat7479 : Unsatisfiable (PosFin 65) f7479 := by
  apply lratCheckerSound f7479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7479
  · intro a ha; simp [p7479] at ha; subst a; trivial
  · exact checked7479
theorem derived7479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7479 := by
  apply localUnsat_implies_entails f7479 [c2283, c1305] c7479 unsat7479 (by rfl) a
  have h0 : Entails.eval a c2283 := h 2282 (by decide)
  have h1 : Entails.eval a c1305 := h 1304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7480 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c761, some c752, some c776, some c753, some c777, some c763, some c767, some c758, some c772, some c7476, some c7478, some c7479, some c903, some c2280, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7480 : lratChecker f7480 p7480 = .success := by decide +kernel
theorem unsat7480 : Unsatisfiable (PosFin 65) f7480 := by
  apply lratCheckerSound f7480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7480
  · intro a ha; simp [p7480] at ha; subst a; trivial
  · exact checked7480
theorem derived7480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7480 := by
  apply localUnsat_implies_entails f7480 [c761, c752, c776, c753, c777, c763, c767, c758, c772, c7476, c7478, c7479, c903, c2280] c7480 unsat7480 (by rfl) a
  have h0 : Entails.eval a c761 := h 760 (by decide)
  have h1 : Entails.eval a c752 := h 751 (by decide)
  have h2 : Entails.eval a c776 := h 775 (by decide)
  have h3 : Entails.eval a c753 := h 752 (by decide)
  have h4 : Entails.eval a c777 := h 776 (by decide)
  have h5 : Entails.eval a c763 := h 762 (by decide)
  have h6 : Entails.eval a c767 := h 766 (by decide)
  have h7 : Entails.eval a c758 := h 757 (by decide)
  have h8 : Entails.eval a c772 := h 771 (by decide)
  have h9 : Entails.eval a c7476 := derived7476 a h
  have h10 : Entails.eval a c7478 := derived7478 a h
  have h11 : Entails.eval a c7479 := derived7479 a h
  have h12 : Entails.eval a c903 := h 902 (by decide)
  have h13 : Entails.eval a c2280 := h 2279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7480

end CochromaticTwenty.Certificates.FixedCore1
