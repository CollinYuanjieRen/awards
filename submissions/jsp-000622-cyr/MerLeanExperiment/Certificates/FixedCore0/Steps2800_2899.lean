import MerLeanExperiment.Certificates.FixedCore0.Steps2700_2799

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10351 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1749, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10351 : lratChecker f10351 p10351 = .success := by decide +kernel
theorem unsat10351 : Unsatisfiable (PosFin 65) f10351 := by
  apply lratCheckerSound f10351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10351
  · intro a ha; simp [p10351] at ha; subst a; trivial
  · exact checked10351
theorem derived10351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10351 := by
  apply localUnsat_implies_entails f10351 [c9748, c1749] c10351 unsat10351 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1749 := h 1748 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10352 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1747, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10352 : lratChecker f10352 p10352 = .success := by decide +kernel
theorem unsat10352 : Unsatisfiable (PosFin 65) f10352 := by
  apply lratCheckerSound f10352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10352
  · intro a ha; simp [p10352] at ha; subst a; trivial
  · exact checked10352
theorem derived10352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10352 := by
  apply localUnsat_implies_entails f10352 [c9748, c1747] c10352 unsat10352 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1747 := h 1746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10353 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1748, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10353 : lratChecker f10353 p10353 = .success := by decide +kernel
theorem unsat10353 : Unsatisfiable (PosFin 65) f10353 := by
  apply lratCheckerSound f10353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10353
  · intro a ha; simp [p10353] at ha; subst a; trivial
  · exact checked10353
theorem derived10353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10353 := by
  apply localUnsat_implies_entails f10353 [c9748, c1748] c10353 unsat10353 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1748 := h 1747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10354 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1745, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10354 : lratChecker f10354 p10354 = .success := by decide +kernel
theorem unsat10354 : Unsatisfiable (PosFin 65) f10354 := by
  apply lratCheckerSound f10354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10354
  · intro a ha; simp [p10354] at ha; subst a; trivial
  · exact checked10354
theorem derived10354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10354 := by
  apply localUnsat_implies_entails f10354 [c9748, c1745] c10354 unsat10354 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1745 := h 1744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10355 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1739, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10355 : lratChecker f10355 p10355 = .success := by decide +kernel
theorem unsat10355 : Unsatisfiable (PosFin 65) f10355 := by
  apply lratCheckerSound f10355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10355
  · intro a ha; simp [p10355] at ha; subst a; trivial
  · exact checked10355
theorem derived10355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10355 := by
  apply localUnsat_implies_entails f10355 [c9748, c1739] c10355 unsat10355 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1739 := h 1738 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10356 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1740, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10356 : lratChecker f10356 p10356 = .success := by decide +kernel
theorem unsat10356 : Unsatisfiable (PosFin 65) f10356 := by
  apply lratCheckerSound f10356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10356
  · intro a ha; simp [p10356] at ha; subst a; trivial
  · exact checked10356
theorem derived10356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10356 := by
  apply localUnsat_implies_entails f10356 [c9748, c1740] c10356 unsat10356 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1740 := h 1739 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10357 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1733, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10357 : lratChecker f10357 p10357 = .success := by decide +kernel
theorem unsat10357 : Unsatisfiable (PosFin 65) f10357 := by
  apply lratCheckerSound f10357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10357
  · intro a ha; simp [p10357] at ha; subst a; trivial
  · exact checked10357
theorem derived10357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10357 := by
  apply localUnsat_implies_entails f10357 [c9748, c1733] c10357 unsat10357 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1733 := h 1732 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10358 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1725, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10358 : lratChecker f10358 p10358 = .success := by decide +kernel
theorem unsat10358 : Unsatisfiable (PosFin 65) f10358 := by
  apply lratCheckerSound f10358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10358
  · intro a ha; simp [p10358] at ha; subst a; trivial
  · exact checked10358
theorem derived10358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10358 := by
  apply localUnsat_implies_entails f10358 [c9748, c1725] c10358 unsat10358 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1725 := h 1724 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10359 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1731, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p10359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10359 : lratChecker f10359 p10359 = .success := by decide +kernel
theorem unsat10359 : Unsatisfiable (PosFin 65) f10359 := by
  apply lratCheckerSound f10359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10359
  · intro a ha; simp [p10359] at ha; subst a; trivial
  · exact checked10359
theorem derived10359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10359 := by
  apply localUnsat_implies_entails f10359 [c9748, c1731] c10359 unsat10359 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1731 := h 1730 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10360 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1732, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10360 : lratChecker f10360 p10360 = .success := by decide +kernel
theorem unsat10360 : Unsatisfiable (PosFin 65) f10360 := by
  apply lratCheckerSound f10360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10360
  · intro a ha; simp [p10360] at ha; subst a; trivial
  · exact checked10360
theorem derived10360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10360 := by
  apply localUnsat_implies_entails f10360 [c9748, c1732] c10360 unsat10360 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1732 := h 1731 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10361 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨62, by decide⟩, true), (⟨6, by decide⟩, true), (⟨61, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1730, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p10361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10361 : lratChecker f10361 p10361 = .success := by decide +kernel
theorem unsat10361 : Unsatisfiable (PosFin 65) f10361 := by
  apply lratCheckerSound f10361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10361
  · intro a ha; simp [p10361] at ha; subst a; trivial
  · exact checked10361
theorem derived10361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10361 := by
  apply localUnsat_implies_entails f10361 [c9748, c1730] c10361 unsat10361 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1730 := h 1729 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10362 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨8, by decide⟩, true), (⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1736, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10362 : lratChecker f10362 p10362 = .success := by decide +kernel
theorem unsat10362 : Unsatisfiable (PosFin 65) f10362 := by
  apply lratCheckerSound f10362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10362
  · intro a ha; simp [p10362] at ha; subst a; trivial
  · exact checked10362
theorem derived10362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10362 := by
  apply localUnsat_implies_entails f10362 [c9748, c1736] c10362 unsat10362 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1736 := h 1735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10363 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1806, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10363 : lratChecker f10363 p10363 = .success := by decide +kernel
theorem unsat10363 : Unsatisfiable (PosFin 65) f10363 := by
  apply lratCheckerSound f10363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10363
  · intro a ha; simp [p10363] at ha; subst a; trivial
  · exact checked10363
theorem derived10363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10363 := by
  apply localUnsat_implies_entails f10363 [c9748, c1806] c10363 unsat10363 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1806 := h 1805 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10364 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1802, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10364 : lratChecker f10364 p10364 = .success := by decide +kernel
theorem unsat10364 : Unsatisfiable (PosFin 65) f10364 := by
  apply lratCheckerSound f10364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10364
  · intro a ha; simp [p10364] at ha; subst a; trivial
  · exact checked10364
theorem derived10364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10364 := by
  apply localUnsat_implies_entails f10364 [c9748, c1802] c10364 unsat10364 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1802 := h 1801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10365 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨60, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1796, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10365 : lratChecker f10365 p10365 = .success := by decide +kernel
theorem unsat10365 : Unsatisfiable (PosFin 65) f10365 := by
  apply lratCheckerSound f10365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10365
  · intro a ha; simp [p10365] at ha; subst a; trivial
  · exact checked10365
theorem derived10365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10365 := by
  apply localUnsat_implies_entails f10365 [c9748, c1796] c10365 unsat10365 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1796 := h 1795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10366 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨57, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1808, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p10366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10366 : lratChecker f10366 p10366 = .success := by decide +kernel
theorem unsat10366 : Unsatisfiable (PosFin 65) f10366 := by
  apply lratCheckerSound f10366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10366
  · intro a ha; simp [p10366] at ha; subst a; trivial
  · exact checked10366
theorem derived10366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10366 := by
  apply localUnsat_implies_entails f10366 [c9748, c1808] c10366 unsat10366 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1808 := h 1807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10367 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1751, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p10367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10367 : lratChecker f10367 p10367 = .success := by decide +kernel
theorem unsat10367 : Unsatisfiable (PosFin 65) f10367 := by
  apply lratCheckerSound f10367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10367
  · intro a ha; simp [p10367] at ha; subst a; trivial
  · exact checked10367
theorem derived10367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10367 := by
  apply localUnsat_implies_entails f10367 [c9748, c1751] c10367 unsat10367 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1751 := h 1750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10368 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, true), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1752, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10368 : lratChecker f10368 p10368 = .success := by decide +kernel
theorem unsat10368 : Unsatisfiable (PosFin 65) f10368 := by
  apply lratCheckerSound f10368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10368
  · intro a ha; simp [p10368] at ha; subst a; trivial
  · exact checked10368
theorem derived10368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10368 := by
  apply localUnsat_implies_entails f10368 [c9748, c1752] c10368 unsat10368 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1752 := h 1751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10369 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1876, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10369 : lratChecker f10369 p10369 = .success := by decide +kernel
theorem unsat10369 : Unsatisfiable (PosFin 65) f10369 := by
  apply lratCheckerSound f10369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10369
  · intro a ha; simp [p10369] at ha; subst a; trivial
  · exact checked10369
theorem derived10369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10369 := by
  apply localUnsat_implies_entails f10369 [c9748, c1876] c10369 unsat10369 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1876 := h 1875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10370 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1728, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10370 : lratChecker f10370 p10370 = .success := by decide +kernel
theorem unsat10370 : Unsatisfiable (PosFin 65) f10370 := by
  apply lratCheckerSound f10370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10370
  · intro a ha; simp [p10370] at ha; subst a; trivial
  · exact checked10370
theorem derived10370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10370 := by
  apply localUnsat_implies_entails f10370 [c9748, c1728] c10370 unsat10370 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1728 := h 1727 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10371 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1801, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10371 : lratChecker f10371 p10371 = .success := by decide +kernel
theorem unsat10371 : Unsatisfiable (PosFin 65) f10371 := by
  apply lratCheckerSound f10371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10371
  · intro a ha; simp [p10371] at ha; subst a; trivial
  · exact checked10371
theorem derived10371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10371 := by
  apply localUnsat_implies_entails f10371 [c9748, c1801] c10371 unsat10371 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1801 := h 1800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10372 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2272, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p10372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10372 : lratChecker f10372 p10372 = .success := by decide +kernel
theorem unsat10372 : Unsatisfiable (PosFin 65) f10372 := by
  apply lratCheckerSound f10372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10372
  · intro a ha; simp [p10372] at ha; subst a; trivial
  · exact checked10372
theorem derived10372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10372 := by
  apply localUnsat_implies_entails f10372 [c9748, c2272] c10372 unsat10372 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2272 := h 2271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10373 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1462, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10373 : lratChecker f10373 p10373 = .success := by decide +kernel
theorem unsat10373 : Unsatisfiable (PosFin 65) f10373 := by
  apply lratCheckerSound f10373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10373
  · intro a ha; simp [p10373] at ha; subst a; trivial
  · exact checked10373
theorem derived10373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10373 := by
  apply localUnsat_implies_entails f10373 [c9748, c1462] c10373 unsat10373 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1462 := h 1461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10374 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1972, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10374 : lratChecker f10374 p10374 = .success := by decide +kernel
theorem unsat10374 : Unsatisfiable (PosFin 65) f10374 := by
  apply lratCheckerSound f10374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10374
  · intro a ha; simp [p10374] at ha; subst a; trivial
  · exact checked10374
theorem derived10374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10374 := by
  apply localUnsat_implies_entails f10374 [c9748, c1972] c10374 unsat10374 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1972 := h 1971 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10375 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1715, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10375 : lratChecker f10375 p10375 = .success := by decide +kernel
theorem unsat10375 : Unsatisfiable (PosFin 65) f10375 := by
  apply lratCheckerSound f10375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10375
  · intro a ha; simp [p10375] at ha; subst a; trivial
  · exact checked10375
theorem derived10375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10375 := by
  apply localUnsat_implies_entails f10375 [c9748, c1715] c10375 unsat10375 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1715 := h 1714 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10376 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1695, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10376 : lratChecker f10376 p10376 = .success := by decide +kernel
theorem unsat10376 : Unsatisfiable (PosFin 65) f10376 := by
  apply lratCheckerSound f10376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10376
  · intro a ha; simp [p10376] at ha; subst a; trivial
  · exact checked10376
theorem derived10376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10376 := by
  apply localUnsat_implies_entails f10376 [c9748, c1695] c10376 unsat10376 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1695 := h 1694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10377 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2186, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10377 : lratChecker f10377 p10377 = .success := by decide +kernel
theorem unsat10377 : Unsatisfiable (PosFin 65) f10377 := by
  apply lratCheckerSound f10377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10377
  · intro a ha; simp [p10377] at ha; subst a; trivial
  · exact checked10377
theorem derived10377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10377 := by
  apply localUnsat_implies_entails f10377 [c9748, c2186] c10377 unsat10377 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2186 := h 2185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10378 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1759, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10378 : lratChecker f10378 p10378 = .success := by decide +kernel
theorem unsat10378 : Unsatisfiable (PosFin 65) f10378 := by
  apply lratCheckerSound f10378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10378
  · intro a ha; simp [p10378] at ha; subst a; trivial
  · exact checked10378
theorem derived10378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10378 := by
  apply localUnsat_implies_entails f10378 [c9748, c1759] c10378 unsat10378 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1759 := h 1758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10379 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1617, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10379 : lratChecker f10379 p10379 = .success := by decide +kernel
theorem unsat10379 : Unsatisfiable (PosFin 65) f10379 := by
  apply lratCheckerSound f10379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10379
  · intro a ha; simp [p10379] at ha; subst a; trivial
  · exact checked10379
theorem derived10379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10379 := by
  apply localUnsat_implies_entails f10379 [c9748, c1617] c10379 unsat10379 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1617 := h 1616 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10380 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1628, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p10380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10380 : lratChecker f10380 p10380 = .success := by decide +kernel
theorem unsat10380 : Unsatisfiable (PosFin 65) f10380 := by
  apply lratCheckerSound f10380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10380
  · intro a ha; simp [p10380] at ha; subst a; trivial
  · exact checked10380
theorem derived10380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10380 := by
  apply localUnsat_implies_entails f10380 [c9748, c1628] c10380 unsat10380 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1628 := h 1627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10381 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2292, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10381 : lratChecker f10381 p10381 = .success := by decide +kernel
theorem unsat10381 : Unsatisfiable (PosFin 65) f10381 := by
  apply lratCheckerSound f10381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10381
  · intro a ha; simp [p10381] at ha; subst a; trivial
  · exact checked10381
theorem derived10381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10381 := by
  apply localUnsat_implies_entails f10381 [c9748, c2292] c10381 unsat10381 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2292 := h 2291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10382 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1471, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p10382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10382 : lratChecker f10382 p10382 = .success := by decide +kernel
theorem unsat10382 : Unsatisfiable (PosFin 65) f10382 := by
  apply lratCheckerSound f10382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10382
  · intro a ha; simp [p10382] at ha; subst a; trivial
  · exact checked10382
theorem derived10382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10382 := by
  apply localUnsat_implies_entails f10382 [c9748, c1471] c10382 unsat10382 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1471 := h 1470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10383 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨14, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2205, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10383 : lratChecker f10383 p10383 = .success := by decide +kernel
theorem unsat10383 : Unsatisfiable (PosFin 65) f10383 := by
  apply lratCheckerSound f10383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10383
  · intro a ha; simp [p10383] at ha; subst a; trivial
  · exact checked10383
theorem derived10383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10383 := by
  apply localUnsat_implies_entails f10383 [c9748, c2205] c10383 unsat10383 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2205 := h 2204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10384 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1616, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10384 : lratChecker f10384 p10384 = .success := by decide +kernel
theorem unsat10384 : Unsatisfiable (PosFin 65) f10384 := by
  apply lratCheckerSound f10384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10384
  · intro a ha; simp [p10384] at ha; subst a; trivial
  · exact checked10384
theorem derived10384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10384 := by
  apply localUnsat_implies_entails f10384 [c9748, c1616] c10384 unsat10384 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1616 := h 1615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10385 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2291, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10385 : lratChecker f10385 p10385 = .success := by decide +kernel
theorem unsat10385 : Unsatisfiable (PosFin 65) f10385 := by
  apply lratCheckerSound f10385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10385
  · intro a ha; simp [p10385] at ha; subst a; trivial
  · exact checked10385
theorem derived10385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10385 := by
  apply localUnsat_implies_entails f10385 [c9748, c2291] c10385 unsat10385 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2291 := h 2290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10386 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1993, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10386 : lratChecker f10386 p10386 = .success := by decide +kernel
theorem unsat10386 : Unsatisfiable (PosFin 65) f10386 := by
  apply lratCheckerSound f10386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10386
  · intro a ha; simp [p10386] at ha; subst a; trivial
  · exact checked10386
theorem derived10386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10386 := by
  apply localUnsat_implies_entails f10386 [c9748, c1993] c10386 unsat10386 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1993 := h 1992 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10387 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2045, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10387 : lratChecker f10387 p10387 = .success := by decide +kernel
theorem unsat10387 : Unsatisfiable (PosFin 65) f10387 := by
  apply lratCheckerSound f10387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10387
  · intro a ha; simp [p10387] at ha; subst a; trivial
  · exact checked10387
theorem derived10387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10387 := by
  apply localUnsat_implies_entails f10387 [c9748, c2045] c10387 unsat10387 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2045 := h 2044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10388 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨14, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2360, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10388 : lratChecker f10388 p10388 = .success := by decide +kernel
theorem unsat10388 : Unsatisfiable (PosFin 65) f10388 := by
  apply lratCheckerSound f10388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10388
  · intro a ha; simp [p10388] at ha; subst a; trivial
  · exact checked10388
theorem derived10388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10388 := by
  apply localUnsat_implies_entails f10388 [c9748, c2360] c10388 unsat10388 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2360 := h 2359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10389 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true), (⟨61, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1513, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10389 : lratChecker f10389 p10389 = .success := by decide +kernel
theorem unsat10389 : Unsatisfiable (PosFin 65) f10389 := by
  apply lratCheckerSound f10389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10389
  · intro a ha; simp [p10389] at ha; subst a; trivial
  · exact checked10389
theorem derived10389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10389 := by
  apply localUnsat_implies_entails f10389 [c9748, c1513] c10389 unsat10389 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1513 := h 1512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10390 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨14, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2359, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10390 : lratChecker f10390 p10390 = .success := by decide +kernel
theorem unsat10390 : Unsatisfiable (PosFin 65) f10390 := by
  apply lratCheckerSound f10390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10390
  · intro a ha; simp [p10390] at ha; subst a; trivial
  · exact checked10390
theorem derived10390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10390 := by
  apply localUnsat_implies_entails f10390 [c9748, c2359] c10390 unsat10390 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2359 := h 2358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10391 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2063, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10391 : lratChecker f10391 p10391 = .success := by decide +kernel
theorem unsat10391 : Unsatisfiable (PosFin 65) f10391 := by
  apply lratCheckerSound f10391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10391
  · intro a ha; simp [p10391] at ha; subst a; trivial
  · exact checked10391
theorem derived10391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10391 := by
  apply localUnsat_implies_entails f10391 [c9748, c2063] c10391 unsat10391 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2063 := h 2062 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10392 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨62, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1504, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10392 : lratChecker f10392 p10392 = .success := by decide +kernel
theorem unsat10392 : Unsatisfiable (PosFin 65) f10392 := by
  apply lratCheckerSound f10392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10392
  · intro a ha; simp [p10392] at ha; subst a; trivial
  · exact checked10392
theorem derived10392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10392 := by
  apply localUnsat_implies_entails f10392 [c9748, c1504] c10392 unsat10392 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1504 := h 1503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10393 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1735, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10393 : lratChecker f10393 p10393 = .success := by decide +kernel
theorem unsat10393 : Unsatisfiable (PosFin 65) f10393 := by
  apply lratCheckerSound f10393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10393
  · intro a ha; simp [p10393] at ha; subst a; trivial
  · exact checked10393
theorem derived10393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10393 := by
  apply localUnsat_implies_entails f10393 [c9748, c1735] c10393 unsat10393 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1735 := h 1734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10394 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1947, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10394 : lratChecker f10394 p10394 = .success := by decide +kernel
theorem unsat10394 : Unsatisfiable (PosFin 65) f10394 := by
  apply lratCheckerSound f10394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10394
  · intro a ha; simp [p10394] at ha; subst a; trivial
  · exact checked10394
theorem derived10394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10394 := by
  apply localUnsat_implies_entails f10394 [c9748, c1947] c10394 unsat10394 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1947 := h 1946 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10395 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1647, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10395 : lratChecker f10395 p10395 = .success := by decide +kernel
theorem unsat10395 : Unsatisfiable (PosFin 65) f10395 := by
  apply lratCheckerSound f10395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10395
  · intro a ha; simp [p10395] at ha; subst a; trivial
  · exact checked10395
theorem derived10395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10395 := by
  apply localUnsat_implies_entails f10395 [c9748, c1647] c10395 unsat10395 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1647 := h 1646 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10396 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨57, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1664, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10396 : lratChecker f10396 p10396 = .success := by decide +kernel
theorem unsat10396 : Unsatisfiable (PosFin 65) f10396 := by
  apply lratCheckerSound f10396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10396
  · intro a ha; simp [p10396] at ha; subst a; trivial
  · exact checked10396
theorem derived10396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10396 := by
  apply localUnsat_implies_entails f10396 [c9748, c1664] c10396 unsat10396 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1664 := h 1663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10397 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1644, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10397 : lratChecker f10397 p10397 = .success := by decide +kernel
theorem unsat10397 : Unsatisfiable (PosFin 65) f10397 := by
  apply lratCheckerSound f10397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10397
  · intro a ha; simp [p10397] at ha; subst a; trivial
  · exact checked10397
theorem derived10397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10397 := by
  apply localUnsat_implies_entails f10397 [c9748, c1644] c10397 unsat10397 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1644 := h 1643 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10398 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1787, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p10398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10398 : lratChecker f10398 p10398 = .success := by decide +kernel
theorem unsat10398 : Unsatisfiable (PosFin 65) f10398 := by
  apply lratCheckerSound f10398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10398
  · intro a ha; simp [p10398] at ha; subst a; trivial
  · exact checked10398
theorem derived10398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10398 := by
  apply localUnsat_implies_entails f10398 [c9748, c1787] c10398 unsat10398 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1787 := h 1786 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10399 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨61, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1885, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10399 : lratChecker f10399 p10399 = .success := by decide +kernel
theorem unsat10399 : Unsatisfiable (PosFin 65) f10399 := by
  apply lratCheckerSound f10399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10399
  · intro a ha; simp [p10399] at ha; subst a; trivial
  · exact checked10399
theorem derived10399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10399 := by
  apply localUnsat_implies_entails f10399 [c9748, c1885] c10399 unsat10399 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1885 := h 1884 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10400 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨61, by decide⟩, true), (⟨55, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1906, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p10400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10400 : lratChecker f10400 p10400 = .success := by decide +kernel
theorem unsat10400 : Unsatisfiable (PosFin 65) f10400 := by
  apply lratCheckerSound f10400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10400
  · intro a ha; simp [p10400] at ha; subst a; trivial
  · exact checked10400
theorem derived10400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10400 := by
  apply localUnsat_implies_entails f10400 [c9748, c1906] c10400 unsat10400 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1906 := h 1905 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10401 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1840, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10401 : lratChecker f10401 p10401 = .success := by decide +kernel
theorem unsat10401 : Unsatisfiable (PosFin 65) f10401 := by
  apply lratCheckerSound f10401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10401
  · intro a ha; simp [p10401] at ha; subst a; trivial
  · exact checked10401
theorem derived10401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10401 := by
  apply localUnsat_implies_entails f10401 [c9748, c1840] c10401 unsat10401 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1840 := h 1839 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10402 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1707, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10402 : lratChecker f10402 p10402 = .success := by decide +kernel
theorem unsat10402 : Unsatisfiable (PosFin 65) f10402 := by
  apply lratCheckerSound f10402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10402
  · intro a ha; simp [p10402] at ha; subst a; trivial
  · exact checked10402
theorem derived10402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10402 := by
  apply localUnsat_implies_entails f10402 [c9748, c1707] c10402 unsat10402 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1707 := h 1706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10403 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1710, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10403 : lratChecker f10403 p10403 = .success := by decide +kernel
theorem unsat10403 : Unsatisfiable (PosFin 65) f10403 := by
  apply lratCheckerSound f10403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10403
  · intro a ha; simp [p10403] at ha; subst a; trivial
  · exact checked10403
theorem derived10403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10403 := by
  apply localUnsat_implies_entails f10403 [c9748, c1710] c10403 unsat10403 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1710 := h 1709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10404 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1708, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p10404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10404 : lratChecker f10404 p10404 = .success := by decide +kernel
theorem unsat10404 : Unsatisfiable (PosFin 65) f10404 := by
  apply lratCheckerSound f10404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10404
  · intro a ha; simp [p10404] at ha; subst a; trivial
  · exact checked10404
theorem derived10404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10404 := by
  apply localUnsat_implies_entails f10404 [c9748, c1708] c10404 unsat10404 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1708 := h 1707 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10405 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1771, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10405 : lratChecker f10405 p10405 = .success := by decide +kernel
theorem unsat10405 : Unsatisfiable (PosFin 65) f10405 := by
  apply lratCheckerSound f10405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10405
  · intro a ha; simp [p10405] at ha; subst a; trivial
  · exact checked10405
theorem derived10405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10405 := by
  apply localUnsat_implies_entails f10405 [c9748, c1771] c10405 unsat10405 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1771 := h 1770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10406 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1865, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10406 : lratChecker f10406 p10406 = .success := by decide +kernel
theorem unsat10406 : Unsatisfiable (PosFin 65) f10406 := by
  apply lratCheckerSound f10406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10406
  · intro a ha; simp [p10406] at ha; subst a; trivial
  · exact checked10406
theorem derived10406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10406 := by
  apply localUnsat_implies_entails f10406 [c9748, c1865] c10406 unsat10406 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1865 := h 1864 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10407 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2302, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10407 : lratChecker f10407 p10407 = .success := by decide +kernel
theorem unsat10407 : Unsatisfiable (PosFin 65) f10407 := by
  apply lratCheckerSound f10407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10407
  · intro a ha; simp [p10407] at ha; subst a; trivial
  · exact checked10407
theorem derived10407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10407 := by
  apply localUnsat_implies_entails f10407 [c9748, c2302] c10407 unsat10407 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2302 := h 2301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10408 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2210, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10408 : lratChecker f10408 p10408 = .success := by decide +kernel
theorem unsat10408 : Unsatisfiable (PosFin 65) f10408 := by
  apply lratCheckerSound f10408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10408
  · intro a ha; simp [p10408] at ha; subst a; trivial
  · exact checked10408
theorem derived10408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10408 := by
  apply localUnsat_implies_entails f10408 [c9748, c2210] c10408 unsat10408 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2210 := h 2209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10409 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1990, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10409 : lratChecker f10409 p10409 = .success := by decide +kernel
theorem unsat10409 : Unsatisfiable (PosFin 65) f10409 := by
  apply lratCheckerSound f10409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10409
  · intro a ha; simp [p10409] at ha; subst a; trivial
  · exact checked10409
theorem derived10409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10409 := by
  apply localUnsat_implies_entails f10409 [c9748, c1990] c10409 unsat10409 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1990 := h 1989 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10410 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1923, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10410 : lratChecker f10410 p10410 = .success := by decide +kernel
theorem unsat10410 : Unsatisfiable (PosFin 65) f10410 := by
  apply lratCheckerSound f10410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10410
  · intro a ha; simp [p10410] at ha; subst a; trivial
  · exact checked10410
theorem derived10410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10410 := by
  apply localUnsat_implies_entails f10410 [c9748, c1923] c10410 unsat10410 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1923 := h 1922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10411 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2281, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10411 : lratChecker f10411 p10411 = .success := by decide +kernel
theorem unsat10411 : Unsatisfiable (PosFin 65) f10411 := by
  apply lratCheckerSound f10411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10411
  · intro a ha; simp [p10411] at ha; subst a; trivial
  · exact checked10411
theorem derived10411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10411 := by
  apply localUnsat_implies_entails f10411 [c9748, c2281] c10411 unsat10411 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2281 := h 2280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10412 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1686, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10412 : lratChecker f10412 p10412 = .success := by decide +kernel
theorem unsat10412 : Unsatisfiable (PosFin 65) f10412 := by
  apply lratCheckerSound f10412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10412
  · intro a ha; simp [p10412] at ha; subst a; trivial
  · exact checked10412
theorem derived10412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10412 := by
  apply localUnsat_implies_entails f10412 [c9748, c1686] c10412 unsat10412 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1686 := h 1685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10413 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1685, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10413 : lratChecker f10413 p10413 = .success := by decide +kernel
theorem unsat10413 : Unsatisfiable (PosFin 65) f10413 := by
  apply lratCheckerSound f10413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10413
  · intro a ha; simp [p10413] at ha; subst a; trivial
  · exact checked10413
theorem derived10413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10413 := by
  apply localUnsat_implies_entails f10413 [c9748, c1685] c10413 unsat10413 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1685 := h 1684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10414 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1980, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10414 : lratChecker f10414 p10414 = .success := by decide +kernel
theorem unsat10414 : Unsatisfiable (PosFin 65) f10414 := by
  apply lratCheckerSound f10414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10414
  · intro a ha; simp [p10414] at ha; subst a; trivial
  · exact checked10414
theorem derived10414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10414 := by
  apply localUnsat_implies_entails f10414 [c9748, c1980] c10414 unsat10414 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1980 := h 1979 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10415 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1850, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10415 : lratChecker f10415 p10415 = .success := by decide +kernel
theorem unsat10415 : Unsatisfiable (PosFin 65) f10415 := by
  apply lratCheckerSound f10415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10415
  · intro a ha; simp [p10415] at ha; subst a; trivial
  · exact checked10415
theorem derived10415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10415 := by
  apply localUnsat_implies_entails f10415 [c9748, c1850] c10415 unsat10415 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1850 := h 1849 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10416 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2294, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10416 : lratChecker f10416 p10416 = .success := by decide +kernel
theorem unsat10416 : Unsatisfiable (PosFin 65) f10416 := by
  apply lratCheckerSound f10416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10416
  · intro a ha; simp [p10416] at ha; subst a; trivial
  · exact checked10416
theorem derived10416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10416 := by
  apply localUnsat_implies_entails f10416 [c9748, c2294] c10416 unsat10416 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2294 := h 2293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10417 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2293, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10417 : lratChecker f10417 p10417 = .success := by decide +kernel
theorem unsat10417 : Unsatisfiable (PosFin 65) f10417 := by
  apply lratCheckerSound f10417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10417
  · intro a ha; simp [p10417] at ha; subst a; trivial
  · exact checked10417
theorem derived10417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10417 := by
  apply localUnsat_implies_entails f10417 [c9748, c2293] c10417 unsat10417 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2293 := h 2292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10418 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2208, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10418 : lratChecker f10418 p10418 = .success := by decide +kernel
theorem unsat10418 : Unsatisfiable (PosFin 65) f10418 := by
  apply lratCheckerSound f10418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10418
  · intro a ha; simp [p10418] at ha; subst a; trivial
  · exact checked10418
theorem derived10418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10418 := by
  apply localUnsat_implies_entails f10418 [c9748, c2208] c10418 unsat10418 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2208 := h 2207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10419 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1926, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p10419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10419 : lratChecker f10419 p10419 = .success := by decide +kernel
theorem unsat10419 : Unsatisfiable (PosFin 65) f10419 := by
  apply lratCheckerSound f10419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10419
  · intro a ha; simp [p10419] at ha; subst a; trivial
  · exact checked10419
theorem derived10419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10419 := by
  apply localUnsat_implies_entails f10419 [c9748, c1926] c10419 unsat10419 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1926 := h 1925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10420 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2043, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10420 : lratChecker f10420 p10420 = .success := by decide +kernel
theorem unsat10420 : Unsatisfiable (PosFin 65) f10420 := by
  apply lratCheckerSound f10420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10420
  · intro a ha; simp [p10420] at ha; subst a; trivial
  · exact checked10420
theorem derived10420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10420 := by
  apply localUnsat_implies_entails f10420 [c9748, c2043] c10420 unsat10420 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2043 := h 2042 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10421 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2191, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10421 : lratChecker f10421 p10421 = .success := by decide +kernel
theorem unsat10421 : Unsatisfiable (PosFin 65) f10421 := by
  apply lratCheckerSound f10421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10421
  · intro a ha; simp [p10421] at ha; subst a; trivial
  · exact checked10421
theorem derived10421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10421 := by
  apply localUnsat_implies_entails f10421 [c9748, c2191] c10421 unsat10421 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2191 := h 2190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10422 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1465, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10422 : lratChecker f10422 p10422 = .success := by decide +kernel
theorem unsat10422 : Unsatisfiable (PosFin 65) f10422 := by
  apply lratCheckerSound f10422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10422
  · intro a ha; simp [p10422] at ha; subst a; trivial
  · exact checked10422
theorem derived10422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10422 := by
  apply localUnsat_implies_entails f10422 [c9748, c1465] c10422 unsat10422 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1465 := h 1464 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10423 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1470, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10423 : lratChecker f10423 p10423 = .success := by decide +kernel
theorem unsat10423 : Unsatisfiable (PosFin 65) f10423 := by
  apply lratCheckerSound f10423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10423
  · intro a ha; simp [p10423] at ha; subst a; trivial
  · exact checked10423
theorem derived10423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10423 := by
  apply localUnsat_implies_entails f10423 [c9748, c1470] c10423 unsat10423 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1470 := h 1469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10424 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1979, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10424 : lratChecker f10424 p10424 = .success := by decide +kernel
theorem unsat10424 : Unsatisfiable (PosFin 65) f10424 := by
  apply lratCheckerSound f10424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10424
  · intro a ha; simp [p10424] at ha; subst a; trivial
  · exact checked10424
theorem derived10424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10424 := by
  apply localUnsat_implies_entails f10424 [c9748, c1979] c10424 unsat10424 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1979 := h 1978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10425 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1683, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10425 : lratChecker f10425 p10425 = .success := by decide +kernel
theorem unsat10425 : Unsatisfiable (PosFin 65) f10425 := by
  apply lratCheckerSound f10425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10425
  · intro a ha; simp [p10425] at ha; subst a; trivial
  · exact checked10425
theorem derived10425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10425 := by
  apply localUnsat_implies_entails f10425 [c9748, c1683] c10425 unsat10425 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1683 := h 1682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10426 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1682, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10426 : lratChecker f10426 p10426 = .success := by decide +kernel
theorem unsat10426 : Unsatisfiable (PosFin 65) f10426 := by
  apply lratCheckerSound f10426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10426
  · intro a ha; simp [p10426] at ha; subst a; trivial
  · exact checked10426
theorem derived10426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10426 := by
  apply localUnsat_implies_entails f10426 [c9748, c1682] c10426 unsat10426 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1682 := h 1681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10427 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1974, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10427 : lratChecker f10427 p10427 = .success := by decide +kernel
theorem unsat10427 : Unsatisfiable (PosFin 65) f10427 := by
  apply lratCheckerSound f10427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10427
  · intro a ha; simp [p10427] at ha; subst a; trivial
  · exact checked10427
theorem derived10427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10427 := by
  apply localUnsat_implies_entails f10427 [c9748, c1974] c10427 unsat10427 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1974 := h 1973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10428 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨6, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1861, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10428 : lratChecker f10428 p10428 = .success := by decide +kernel
theorem unsat10428 : Unsatisfiable (PosFin 65) f10428 := by
  apply lratCheckerSound f10428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10428
  · intro a ha; simp [p10428] at ha; subst a; trivial
  · exact checked10428
theorem derived10428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10428 := by
  apply localUnsat_implies_entails f10428 [c9748, c1861] c10428 unsat10428 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1861 := h 1860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10429 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2213, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10429 : lratChecker f10429 p10429 = .success := by decide +kernel
theorem unsat10429 : Unsatisfiable (PosFin 65) f10429 := by
  apply lratCheckerSound f10429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10429
  · intro a ha; simp [p10429] at ha; subst a; trivial
  · exact checked10429
theorem derived10429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10429 := by
  apply localUnsat_implies_entails f10429 [c9748, c2213] c10429 unsat10429 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2213 := h 2212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10430 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2288, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10430 : lratChecker f10430 p10430 = .success := by decide +kernel
theorem unsat10430 : Unsatisfiable (PosFin 65) f10430 := by
  apply lratCheckerSound f10430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10430
  · intro a ha; simp [p10430] at ha; subst a; trivial
  · exact checked10430
theorem derived10430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10430 := by
  apply localUnsat_implies_entails f10430 [c9748, c2288] c10430 unsat10430 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2288 := h 2287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10431 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2289, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10431 : lratChecker f10431 p10431 = .success := by decide +kernel
theorem unsat10431 : Unsatisfiable (PosFin 65) f10431 := by
  apply lratCheckerSound f10431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10431
  · intro a ha; simp [p10431] at ha; subst a; trivial
  · exact checked10431
theorem derived10431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10431 := by
  apply localUnsat_implies_entails f10431 [c9748, c2289] c10431 unsat10431 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2289 := h 2288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10432 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1859, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10432 : lratChecker f10432 p10432 = .success := by decide +kernel
theorem unsat10432 : Unsatisfiable (PosFin 65) f10432 := by
  apply lratCheckerSound f10432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10432
  · intro a ha; simp [p10432] at ha; subst a; trivial
  · exact checked10432
theorem derived10432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10432 := by
  apply localUnsat_implies_entails f10432 [c9748, c1859] c10432 unsat10432 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1859 := h 1858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10433 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1692, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10433 : lratChecker f10433 p10433 = .success := by decide +kernel
theorem unsat10433 : Unsatisfiable (PosFin 65) f10433 := by
  apply lratCheckerSound f10433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10433
  · intro a ha; simp [p10433] at ha; subst a; trivial
  · exact checked10433
theorem derived10433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10433 := by
  apply localUnsat_implies_entails f10433 [c9748, c1692] c10433 unsat10433 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1692 := h 1691 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10434 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10434 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1986, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10434 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10434 : lratChecker f10434 p10434 = .success := by decide +kernel
theorem unsat10434 : Unsatisfiable (PosFin 65) f10434 := by
  apply lratCheckerSound f10434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10434
  · intro a ha; simp [p10434] at ha; subst a; trivial
  · exact checked10434
theorem derived10434 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10434 := by
  apply localUnsat_implies_entails f10434 [c9748, c1986] c10434 unsat10434 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1986 := h 1985 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10435 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10435 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1858, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10435 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10435 : lratChecker f10435 p10435 = .success := by decide +kernel
theorem unsat10435 : Unsatisfiable (PosFin 65) f10435 := by
  apply lratCheckerSound f10435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10435
  · intro a ha; simp [p10435] at ha; subst a; trivial
  · exact checked10435
theorem derived10435 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10435 := by
  apply localUnsat_implies_entails f10435 [c9748, c1858] c10435 unsat10435 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1858 := h 1857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10436 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10436 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2299, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p10436 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10436 : lratChecker f10436 p10436 = .success := by decide +kernel
theorem unsat10436 : Unsatisfiable (PosFin 65) f10436 := by
  apply lratCheckerSound f10436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10436
  · intro a ha; simp [p10436] at ha; subst a; trivial
  · exact checked10436
theorem derived10436 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10436 := by
  apply localUnsat_implies_entails f10436 [c9748, c2299] c10436 unsat10436 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2299 := h 2298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10437 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10437 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2297, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10437 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10437 : lratChecker f10437 p10437 = .success := by decide +kernel
theorem unsat10437 : Unsatisfiable (PosFin 65) f10437 := by
  apply lratCheckerSound f10437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10437
  · intro a ha; simp [p10437] at ha; subst a; trivial
  · exact checked10437
theorem derived10437 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10437 := by
  apply localUnsat_implies_entails f10437 [c9748, c2297] c10437 unsat10437 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2297 := h 2296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10438 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10438 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1855, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10438 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10438 : lratChecker f10438 p10438 = .success := by decide +kernel
theorem unsat10438 : Unsatisfiable (PosFin 65) f10438 := by
  apply lratCheckerSound f10438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10438
  · intro a ha; simp [p10438] at ha; subst a; trivial
  · exact checked10438
theorem derived10438 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10438 := by
  apply localUnsat_implies_entails f10438 [c9748, c1855] c10438 unsat10438 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1855 := h 1854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10439 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10439 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2277, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10439 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10439 : lratChecker f10439 p10439 = .success := by decide +kernel
theorem unsat10439 : Unsatisfiable (PosFin 65) f10439 := by
  apply lratCheckerSound f10439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10439
  · intro a ha; simp [p10439] at ha; subst a; trivial
  · exact checked10439
theorem derived10439 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10439 := by
  apply localUnsat_implies_entails f10439 [c9748, c2277] c10439 unsat10439 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2277 := h 2276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10440 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10440 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2044, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10440 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10440 : lratChecker f10440 p10440 = .success := by decide +kernel
theorem unsat10440 : Unsatisfiable (PosFin 65) f10440 := by
  apply lratCheckerSound f10440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10440
  · intro a ha; simp [p10440] at ha; subst a; trivial
  · exact checked10440
theorem derived10440 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10440 := by
  apply localUnsat_implies_entails f10440 [c9748, c2044] c10440 unsat10440 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2044 := h 2043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10441 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨28, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10441 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1477, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10441 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10441 : lratChecker f10441 p10441 = .success := by decide +kernel
theorem unsat10441 : Unsatisfiable (PosFin 65) f10441 := by
  apply lratCheckerSound f10441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10441
  · intro a ha; simp [p10441] at ha; subst a; trivial
  · exact checked10441
theorem derived10441 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10441 := by
  apply localUnsat_implies_entails f10441 [c9748, c1477] c10441 unsat10441 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1477 := h 1476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10442 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10442 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1625, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10442 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10442 : lratChecker f10442 p10442 = .success := by decide +kernel
theorem unsat10442 : Unsatisfiable (PosFin 65) f10442 := by
  apply lratCheckerSound f10442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10442
  · intro a ha; simp [p10442] at ha; subst a; trivial
  · exact checked10442
theorem derived10442 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10442 := by
  apply localUnsat_implies_entails f10442 [c9748, c1625] c10442 unsat10442 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1625 := h 1624 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10443 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10443 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1622, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10443 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10443 : lratChecker f10443 p10443 = .success := by decide +kernel
theorem unsat10443 : Unsatisfiable (PosFin 65) f10443 := by
  apply lratCheckerSound f10443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10443
  · intro a ha; simp [p10443] at ha; subst a; trivial
  · exact checked10443
theorem derived10443 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10443 := by
  apply localUnsat_implies_entails f10443 [c9748, c1622] c10443 unsat10443 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1622 := h 1621 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10444 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10444 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1983, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10444 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10444 : lratChecker f10444 p10444 = .success := by decide +kernel
theorem unsat10444 : Unsatisfiable (PosFin 65) f10444 := by
  apply lratCheckerSound f10444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10444
  · intro a ha; simp [p10444] at ha; subst a; trivial
  · exact checked10444
theorem derived10444 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10444 := by
  apply localUnsat_implies_entails f10444 [c9748, c1983] c10444 unsat10444 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1983 := h 1982 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10445 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10445 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1474, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10445 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10445 : lratChecker f10445 p10445 = .success := by decide +kernel
theorem unsat10445 : Unsatisfiable (PosFin 65) f10445 := by
  apply lratCheckerSound f10445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10445
  · intro a ha; simp [p10445] at ha; subst a; trivial
  · exact checked10445
theorem derived10445 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10445 := by
  apply localUnsat_implies_entails f10445 [c9748, c1474] c10445 unsat10445 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1474 := h 1473 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10446 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10446 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1699, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10446 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10446 : lratChecker f10446 p10446 = .success := by decide +kernel
theorem unsat10446 : Unsatisfiable (PosFin 65) f10446 := by
  apply lratCheckerSound f10446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10446
  · intro a ha; simp [p10446] at ha; subst a; trivial
  · exact checked10446
theorem derived10446 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10446 := by
  apply localUnsat_implies_entails f10446 [c9748, c1699] c10446 unsat10446 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1699 := h 1698 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10447 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10447 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2279, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10447 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10447 : lratChecker f10447 p10447 = .success := by decide +kernel
theorem unsat10447 : Unsatisfiable (PosFin 65) f10447 := by
  apply lratCheckerSound f10447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10447
  · intro a ha; simp [p10447] at ha; subst a; trivial
  · exact checked10447
theorem derived10447 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10447 := by
  apply localUnsat_implies_entails f10447 [c9748, c2279] c10447 unsat10447 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2279 := h 2278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10448 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10448 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1475, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10448 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10448 : lratChecker f10448 p10448 = .success := by decide +kernel
theorem unsat10448 : Unsatisfiable (PosFin 65) f10448 := by
  apply lratCheckerSound f10448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10448
  · intro a ha; simp [p10448] at ha; subst a; trivial
  · exact checked10448
theorem derived10448 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10448 := by
  apply localUnsat_implies_entails f10448 [c9748, c1475] c10448 unsat10448 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1475 := h 1474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10449 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10449 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1984, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10449 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10449 : lratChecker f10449 p10449 = .success := by decide +kernel
theorem unsat10449 : Unsatisfiable (PosFin 65) f10449 := by
  apply lratCheckerSound f10449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10449
  · intro a ha; simp [p10449] at ha; subst a; trivial
  · exact checked10449
theorem derived10449 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10449 := by
  apply localUnsat_implies_entails f10449 [c9748, c1984] c10449 unsat10449 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1984 := h 1983 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10450 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10450 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2202, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10450 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10450 : lratChecker f10450 p10450 = .success := by decide +kernel
theorem unsat10450 : Unsatisfiable (PosFin 65) f10450 := by
  apply lratCheckerSound f10450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10450
  · intro a ha; simp [p10450] at ha; subst a; trivial
  · exact checked10450
theorem derived10450 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10450 := by
  apply localUnsat_implies_entails f10450 [c9748, c2202] c10450 unsat10450 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2202 := h 2201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived10450

end CochromaticTwenty.Certificates.FixedCore0
