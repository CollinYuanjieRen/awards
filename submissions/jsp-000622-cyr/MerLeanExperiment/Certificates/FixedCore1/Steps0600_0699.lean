import MerLeanExperiment.Certificates.FixedCore1.Steps0500_0599

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6481 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6371, some c6227, some c6468, some c6478, some c6479, some c6480, some c4258, some c4235, some c5378, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6481 : lratChecker f6481 p6481 = .success := by decide +kernel
theorem unsat6481 : Unsatisfiable (PosFin 65) f6481 := by
  apply lratCheckerSound f6481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6481
  · intro a ha; simp [p6481] at ha; subst a; trivial
  · exact checked6481
theorem derived6481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6481 := by
  apply localUnsat_implies_entails f6481 [c6440, c6371, c6227, c6468, c6478, c6479, c6480, c4258, c4235, c5378] c6481 unsat6481 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6468 := derived6468 a h
  have h4 : Entails.eval a c6478 := derived6478 a h
  have h5 : Entails.eval a c6479 := derived6479 a h
  have h6 : Entails.eval a c6480 := derived6480 a h
  have h7 : Entails.eval a c4258 := h 4257 (by decide)
  have h8 : Entails.eval a c4235 := h 4234 (by decide)
  have h9 : Entails.eval a c5378 := h 5377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6482 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨64, by decide⟩, false), (⟨58, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3483, some c3429, some c3457, some c4839, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p6482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6482 : lratChecker f6482 p6482 = .success := by decide +kernel
theorem unsat6482 : Unsatisfiable (PosFin 65) f6482 := by
  apply lratCheckerSound f6482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6482
  · intro a ha; simp [p6482] at ha; subst a; trivial
  · exact checked6482
theorem derived6482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6482 := by
  apply localUnsat_implies_entails f6482 [c3483, c3429, c3457, c4839] c6482 unsat6482 (by rfl) a
  have h0 : Entails.eval a c3483 := h 3482 (by decide)
  have h1 : Entails.eval a c3429 := h 3428 (by decide)
  have h2 : Entails.eval a c3457 := h 3456 (by decide)
  have h3 : Entails.eval a c4839 := h 4838 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6483 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6483 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6481, some c4961, some c4135, some c3613, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6483 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6483 : lratChecker f6483 p6483 = .success := by decide +kernel
theorem unsat6483 : Unsatisfiable (PosFin 65) f6483 := by
  apply lratCheckerSound f6483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6483
  · intro a ha; simp [p6483] at ha; subst a; trivial
  · exact checked6483
theorem derived6483 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6483 := by
  apply localUnsat_implies_entails f6483 [c6481, c4961, c4135, c3613] c6483 unsat6483 (by rfl) a
  have h0 : Entails.eval a c6481 := derived6481 a h
  have h1 : Entails.eval a c4961 := h 4960 (by decide)
  have h2 : Entails.eval a c4135 := h 4134 (by decide)
  have h3 : Entails.eval a c3613 := h 3612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6484 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨33, by decide⟩, true), (⟨58, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6484 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6281, some c4761, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6484 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6484 : lratChecker f6484 p6484 = .success := by decide +kernel
theorem unsat6484 : Unsatisfiable (PosFin 65) f6484 := by
  apply lratCheckerSound f6484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6484
  · intro a ha; simp [p6484] at ha; subst a; trivial
  · exact checked6484
theorem derived6484 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6484 := by
  apply localUnsat_implies_entails f6484 [c6281, c4761] c6484 unsat6484 (by rfl) a
  have h0 : Entails.eval a c6281 := derived6281 a h
  have h1 : Entails.eval a c4761 := h 4760 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6485 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false), (⟨58, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6485 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4076, some c5410, some c4716, some c3977, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p6485 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6485 : lratChecker f6485 p6485 = .success := by decide +kernel
theorem unsat6485 : Unsatisfiable (PosFin 65) f6485 := by
  apply lratCheckerSound f6485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6485
  · intro a ha; simp [p6485] at ha; subst a; trivial
  · exact checked6485
theorem derived6485 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6485 := by
  apply localUnsat_implies_entails f6485 [c4076, c5410, c4716, c3977] c6485 unsat6485 (by rfl) a
  have h0 : Entails.eval a c4076 := h 4075 (by decide)
  have h1 : Entails.eval a c5410 := h 5409 (by decide)
  have h2 : Entails.eval a c4716 := h 4715 (by decide)
  have h3 : Entails.eval a c3977 := h 3976 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6486 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6486 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6481, some c6485, some c6482, some c6483, some c6484, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6486 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6486 : lratChecker f6486 p6486 = .success := by decide +kernel
theorem unsat6486 : Unsatisfiable (PosFin 65) f6486 := by
  apply lratCheckerSound f6486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6486
  · intro a ha; simp [p6486] at ha; subst a; trivial
  · exact checked6486
theorem derived6486 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6486 := by
  apply localUnsat_implies_entails f6486 [c6440, c6481, c6485, c6482, c6483, c6484] c6486 unsat6486 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6481 := derived6481 a h
  have h2 : Entails.eval a c6485 := derived6485 a h
  have h3 : Entails.eval a c6482 := derived6482 a h
  have h4 : Entails.eval a c6483 := derived6483 a h
  have h5 : Entails.eval a c6484 := derived6484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6487 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6487 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6481, some c6485, some c6486, some c4259, some c5325, some c5443, some c5608, some c6371, some c5381, some c5729, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6487 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6487 : lratChecker f6487 p6487 = .success := by decide +kernel
theorem unsat6487 : Unsatisfiable (PosFin 65) f6487 := by
  apply lratCheckerSound f6487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6487
  · intro a ha; simp [p6487] at ha; subst a; trivial
  · exact checked6487
theorem derived6487 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6487 := by
  apply localUnsat_implies_entails f6487 [c6440, c6481, c6485, c6486, c4259, c5325, c5443, c5608, c6371, c5381, c5729] c6487 unsat6487 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6481 := derived6481 a h
  have h2 : Entails.eval a c6485 := derived6485 a h
  have h3 : Entails.eval a c6486 := derived6486 a h
  have h4 : Entails.eval a c4259 := h 4258 (by decide)
  have h5 : Entails.eval a c5325 := h 5324 (by decide)
  have h6 : Entails.eval a c5443 := h 5442 (by decide)
  have h7 : Entails.eval a c5608 := h 5607 (by decide)
  have h8 : Entails.eval a c6371 := derived6371 a h
  have h9 : Entails.eval a c5381 := h 5380 (by decide)
  have h10 : Entails.eval a c5729 := h 5728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6488 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6488 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6481, some c6485, some c6486, some c4259, some c5325, some c5443, some c5608, some c6371, some c5005, some c6236, some c6487, some c5165, some c5659, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6488 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6488 : lratChecker f6488 p6488 = .success := by decide +kernel
theorem unsat6488 : Unsatisfiable (PosFin 65) f6488 := by
  apply lratCheckerSound f6488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6488
  · intro a ha; simp [p6488] at ha; subst a; trivial
  · exact checked6488
theorem derived6488 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6488 := by
  apply localUnsat_implies_entails f6488 [c6440, c6481, c6485, c6486, c4259, c5325, c5443, c5608, c6371, c5005, c6236, c6487, c5165, c5659] c6488 unsat6488 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6481 := derived6481 a h
  have h2 : Entails.eval a c6485 := derived6485 a h
  have h3 : Entails.eval a c6486 := derived6486 a h
  have h4 : Entails.eval a c4259 := h 4258 (by decide)
  have h5 : Entails.eval a c5325 := h 5324 (by decide)
  have h6 : Entails.eval a c5443 := h 5442 (by decide)
  have h7 : Entails.eval a c5608 := h 5607 (by decide)
  have h8 : Entails.eval a c6371 := derived6371 a h
  have h9 : Entails.eval a c5005 := h 5004 (by decide)
  have h10 : Entails.eval a c6236 := derived6236 a h
  have h11 : Entails.eval a c6487 := derived6487 a h
  have h12 : Entails.eval a c5165 := h 5164 (by decide)
  have h13 : Entails.eval a c5659 := h 5658 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6489 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6489 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6485, some c6486, some c4259, some c5325, some c5443, some c5608, some c6488, some c5757, some c5514, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p6489 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6489 : lratChecker f6489 p6489 = .success := by decide +kernel
theorem unsat6489 : Unsatisfiable (PosFin 65) f6489 := by
  apply lratCheckerSound f6489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6489
  · intro a ha; simp [p6489] at ha; subst a; trivial
  · exact checked6489
theorem derived6489 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6489 := by
  apply localUnsat_implies_entails f6489 [c6485, c6486, c4259, c5325, c5443, c5608, c6488, c5757, c5514] c6489 unsat6489 (by rfl) a
  have h0 : Entails.eval a c6485 := derived6485 a h
  have h1 : Entails.eval a c6486 := derived6486 a h
  have h2 : Entails.eval a c4259 := h 4258 (by decide)
  have h3 : Entails.eval a c5325 := h 5324 (by decide)
  have h4 : Entails.eval a c5443 := h 5442 (by decide)
  have h5 : Entails.eval a c5608 := h 5607 (by decide)
  have h6 : Entails.eval a c6488 := derived6488 a h
  have h7 : Entails.eval a c5757 := h 5756 (by decide)
  have h8 : Entails.eval a c5514 := h 5513 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6490 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6490 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6440, some c6481, some c6489, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6490 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6490 : lratChecker f6490 p6490 = .success := by decide +kernel
theorem unsat6490 : Unsatisfiable (PosFin 65) f6490 := by
  apply lratCheckerSound f6490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6490
  · intro a ha; simp [p6490] at ha; subst a; trivial
  · exact checked6490
theorem derived6490 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6490 := by
  apply localUnsat_implies_entails f6490 [c6440, c6481, c6489] c6490 unsat6490 (by rfl) a
  have h0 : Entails.eval a c6440 := derived6440 a h
  have h1 : Entails.eval a c6481 := derived6481 a h
  have h2 : Entails.eval a c6489 := derived6489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6491 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6491 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c5732, some c5731, some c5733, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6491 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6491 : lratChecker f6491 p6491 = .success := by decide +kernel
theorem unsat6491 : Unsatisfiable (PosFin 65) f6491 := by
  apply lratCheckerSound f6491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6491
  · intro a ha; simp [p6491] at ha; subst a; trivial
  · exact checked6491
theorem derived6491 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6491 := by
  apply localUnsat_implies_entails f6491 [c6371, c5732, c5731, c5733] c6491 unsat6491 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c5732 := h 5731 (by decide)
  have h2 : Entails.eval a c5731 := h 5730 (by decide)
  have h3 : Entails.eval a c5733 := h 5732 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6492 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6492 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c4157, some c4160, some c4162, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6492 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6492 : lratChecker f6492 p6492 = .success := by decide +kernel
theorem unsat6492 : Unsatisfiable (PosFin 65) f6492 := by
  apply lratCheckerSound f6492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6492
  · intro a ha; simp [p6492] at ha; subst a; trivial
  · exact checked6492
theorem derived6492 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6492 := by
  apply localUnsat_implies_entails f6492 [c6371, c4157, c4160, c4162] c6492 unsat6492 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c4157 := h 4156 (by decide)
  have h2 : Entails.eval a c4160 := h 4159 (by decide)
  have h3 : Entails.eval a c4162 := h 4161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6493 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6493 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6371, some c6227, some c4232, some c4239, some c4240, some c6492, some c4250, some c4277, some c4092, some c5337, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6493 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6493 : lratChecker f6493 p6493 = .success := by decide +kernel
theorem unsat6493 : Unsatisfiable (PosFin 65) f6493 := by
  apply lratCheckerSound f6493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6493
  · intro a ha; simp [p6493] at ha; subst a; trivial
  · exact checked6493
theorem derived6493 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6493 := by
  apply localUnsat_implies_entails f6493 [c6490, c6371, c6227, c4232, c4239, c4240, c6492, c4250, c4277, c4092, c5337] c6493 unsat6493 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c4232 := h 4231 (by decide)
  have h4 : Entails.eval a c4239 := h 4238 (by decide)
  have h5 : Entails.eval a c4240 := h 4239 (by decide)
  have h6 : Entails.eval a c6492 := derived6492 a h
  have h7 : Entails.eval a c4250 := h 4249 (by decide)
  have h8 : Entails.eval a c4277 := h 4276 (by decide)
  have h9 : Entails.eval a c4092 := h 4091 (by decide)
  have h10 : Entails.eval a c5337 := h 5336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6494 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6494 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c4092, some c5337, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6494 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6494 : lratChecker f6494 p6494 = .success := by decide +kernel
theorem unsat6494 : Unsatisfiable (PosFin 65) f6494 := by
  apply lratCheckerSound f6494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6494
  · intro a ha; simp [p6494] at ha; subst a; trivial
  · exact checked6494
theorem derived6494 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6494 := by
  apply localUnsat_implies_entails f6494 [c6490, c6227, c4092, c5337] c6494 unsat6494 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4092 := h 4091 (by decide)
  have h3 : Entails.eval a c5337 := h 5336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6495 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨52, by decide⟩, true), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6495 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c5381, some c5384, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6495 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6495 : lratChecker f6495 p6495 = .success := by decide +kernel
theorem unsat6495 : Unsatisfiable (PosFin 65) f6495 := by
  apply lratCheckerSound f6495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6495
  · intro a ha; simp [p6495] at ha; subst a; trivial
  · exact checked6495
theorem derived6495 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6495 := by
  apply localUnsat_implies_entails f6495 [c6371, c5381, c5384] c6495 unsat6495 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c5381 := h 5380 (by decide)
  have h2 : Entails.eval a c5384 := h 5383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6496 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6496 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c4084, some c4092, some c4085, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6496 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6496 : lratChecker f6496 p6496 = .success := by decide +kernel
theorem unsat6496 : Unsatisfiable (PosFin 65) f6496 := by
  apply lratCheckerSound f6496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6496
  · intro a ha; simp [p6496] at ha; subst a; trivial
  · exact checked6496
theorem derived6496 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6496 := by
  apply localUnsat_implies_entails f6496 [c6490, c6227, c4084, c4092, c4085] c6496 unsat6496 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4084 := h 4083 (by decide)
  have h3 : Entails.eval a c4092 := h 4091 (by decide)
  have h4 : Entails.eval a c4085 := h 4084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6497 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨64, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6497 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5375, some c6495, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p6497 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6497 : lratChecker f6497 p6497 = .success := by decide +kernel
theorem unsat6497 : Unsatisfiable (PosFin 65) f6497 := by
  apply lratCheckerSound f6497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6497
  · intro a ha; simp [p6497] at ha; subst a; trivial
  · exact checked6497
theorem derived6497 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6497 := by
  apply localUnsat_implies_entails f6497 [c5375, c6495] c6497 unsat6497 (by rfl) a
  have h0 : Entails.eval a c5375 := h 5374 (by decide)
  have h1 : Entails.eval a c6495 := derived6495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6498 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨63, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6498 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4269, some c4277, some c4274, some c4267, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6498 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6498 : lratChecker f6498 p6498 = .success := by decide +kernel
theorem unsat6498 : Unsatisfiable (PosFin 65) f6498 := by
  apply lratCheckerSound f6498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6498
  · intro a ha; simp [p6498] at ha; subst a; trivial
  · exact checked6498
theorem derived6498 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6498 := by
  apply localUnsat_implies_entails f6498 [c4269, c4277, c4274, c4267] c6498 unsat6498 (by rfl) a
  have h0 : Entails.eval a c4269 := h 4268 (by decide)
  have h1 : Entails.eval a c4277 := h 4276 (by decide)
  have h2 : Entails.eval a c4274 := h 4273 (by decide)
  have h3 : Entails.eval a c4267 := h 4266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6499 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6499 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6493, some c6496, some c6497, some c6498, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6499 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6499 : lratChecker f6499 p6499 = .success := by decide +kernel
theorem unsat6499 : Unsatisfiable (PosFin 65) f6499 := by
  apply lratCheckerSound f6499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6499
  · intro a ha; simp [p6499] at ha; subst a; trivial
  · exact checked6499
theorem derived6499 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6499 := by
  apply localUnsat_implies_entails f6499 [c6490, c6227, c6493, c6496, c6497, c6498] c6499 unsat6499 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6493 := derived6493 a h
  have h3 : Entails.eval a c6496 := derived6496 a h
  have h4 : Entails.eval a c6497 := derived6497 a h
  have h5 : Entails.eval a c6498 := derived6498 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6500 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6500 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6371, some c5268, some c5263, some c5365, some c5220, some c4964, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6500 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6500 : lratChecker f6500 p6500 = .success := by decide +kernel
theorem unsat6500 : Unsatisfiable (PosFin 65) f6500 := by
  apply lratCheckerSound f6500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6500
  · intro a ha; simp [p6500] at ha; subst a; trivial
  · exact checked6500
theorem derived6500 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6500 := by
  apply localUnsat_implies_entails f6500 [c6490, c6371, c5268, c5263, c5365, c5220, c4964] c6500 unsat6500 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c5268 := h 5267 (by decide)
  have h3 : Entails.eval a c5263 := h 5262 (by decide)
  have h4 : Entails.eval a c5365 := h 5364 (by decide)
  have h5 : Entails.eval a c5220 := h 5219 (by decide)
  have h6 : Entails.eval a c4964 := h 4963 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6501 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨58, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6501 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5543, some c5549, some c5548, some c5542, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6501 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6501 : lratChecker f6501 p6501 = .success := by decide +kernel
theorem unsat6501 : Unsatisfiable (PosFin 65) f6501 := by
  apply lratCheckerSound f6501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6501
  · intro a ha; simp [p6501] at ha; subst a; trivial
  · exact checked6501
theorem derived6501 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6501 := by
  apply localUnsat_implies_entails f6501 [c5543, c5549, c5548, c5542] c6501 unsat6501 (by rfl) a
  have h0 : Entails.eval a c5543 := h 5542 (by decide)
  have h1 : Entails.eval a c5549 := h 5548 (by decide)
  have h2 : Entails.eval a c5548 := h 5547 (by decide)
  have h3 : Entails.eval a c5542 := h 5541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6502 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, false), (⟨41, by decide⟩, true), (⟨36, by decide⟩, false), (⟨61, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6502 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5747, some c4367, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p6502 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6502 : lratChecker f6502 p6502 = .success := by decide +kernel
theorem unsat6502 : Unsatisfiable (PosFin 65) f6502 := by
  apply lratCheckerSound f6502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6502
  · intro a ha; simp [p6502] at ha; subst a; trivial
  · exact checked6502
theorem derived6502 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6502 := by
  apply localUnsat_implies_entails f6502 [c5747, c4367] c6502 unsat6502 (by rfl) a
  have h0 : Entails.eval a c5747 := h 5746 (by decide)
  have h1 : Entails.eval a c4367 := h 4366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6503 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨53, by decide⟩, false), (⟨42, by decide⟩, true), (⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨34, by decide⟩, false), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6503 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6490, some c6501, some c4868, some c6466, some c4121, some c3435, some c4547, some c5615, some c5309, some c6502, some c5879, some c3598, some c5044, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6503 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6503 : lratChecker f6503 p6503 = .success := by decide +kernel
theorem unsat6503 : Unsatisfiable (PosFin 65) f6503 := by
  apply lratCheckerSound f6503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6503
  · intro a ha; simp [p6503] at ha; subst a; trivial
  · exact checked6503
theorem derived6503 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6503 := by
  apply localUnsat_implies_entails f6503 [c6227, c6490, c6501, c4868, c6466, c4121, c3435, c4547, c5615, c5309, c6502, c5879, c3598, c5044] c6503 unsat6503 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6501 := derived6501 a h
  have h3 : Entails.eval a c4868 := h 4867 (by decide)
  have h4 : Entails.eval a c6466 := derived6466 a h
  have h5 : Entails.eval a c4121 := h 4120 (by decide)
  have h6 : Entails.eval a c3435 := h 3434 (by decide)
  have h7 : Entails.eval a c4547 := h 4546 (by decide)
  have h8 : Entails.eval a c5615 := h 5614 (by decide)
  have h9 : Entails.eval a c5309 := h 5308 (by decide)
  have h10 : Entails.eval a c6502 := derived6502 a h
  have h11 : Entails.eval a c5879 := h 5878 (by decide)
  have h12 : Entails.eval a c3598 := h 3597 (by decide)
  have h13 : Entails.eval a c5044 := h 5043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6504 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨39, by decide⟩, false), (⟨46, by decide⟩, true), (⟨34, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6504 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6304, some c6302, some c3504, some c3451, some c4690, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6504 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6504 : lratChecker f6504 p6504 = .success := by decide +kernel
theorem unsat6504 : Unsatisfiable (PosFin 65) f6504 := by
  apply lratCheckerSound f6504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6504
  · intro a ha; simp [p6504] at ha; subst a; trivial
  · exact checked6504
theorem derived6504 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6504 := by
  apply localUnsat_implies_entails f6504 [c6490, c6227, c6304, c6302, c3504, c3451, c4690] c6504 unsat6504 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6304 := derived6304 a h
  have h3 : Entails.eval a c6302 := derived6302 a h
  have h4 : Entails.eval a c3504 := h 3503 (by decide)
  have h5 : Entails.eval a c3451 := h 3450 (by decide)
  have h6 : Entails.eval a c4690 := h 4689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6505 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨46, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6505 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c5878, some c4843, some c4522, some c4368, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6505 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6505 : lratChecker f6505 p6505 = .success := by decide +kernel
theorem unsat6505 : Unsatisfiable (PosFin 65) f6505 := by
  apply lratCheckerSound f6505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6505
  · intro a ha; simp [p6505] at ha; subst a; trivial
  · exact checked6505
theorem derived6505 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6505 := by
  apply localUnsat_implies_entails f6505 [c6490, c6227, c5878, c4843, c4522, c4368] c6505 unsat6505 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5878 := h 5877 (by decide)
  have h3 : Entails.eval a c4843 := h 4842 (by decide)
  have h4 : Entails.eval a c4522 := h 4521 (by decide)
  have h5 : Entails.eval a c4368 := h 4367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6506 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6506 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6499, some c6227, some c6490, some c6501, some c6504, some c6500, some c6503, some c4119, some c6505, some c3491, some c5308, some c6306, some c4800, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6506 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6506 : lratChecker f6506 p6506 = .success := by decide +kernel
theorem unsat6506 : Unsatisfiable (PosFin 65) f6506 := by
  apply lratCheckerSound f6506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6506
  · intro a ha; simp [p6506] at ha; subst a; trivial
  · exact checked6506
theorem derived6506 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6506 := by
  apply localUnsat_implies_entails f6506 [c6499, c6227, c6490, c6501, c6504, c6500, c6503, c4119, c6505, c3491, c5308, c6306, c4800] c6506 unsat6506 (by rfl) a
  have h0 : Entails.eval a c6499 := derived6499 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6501 := derived6501 a h
  have h4 : Entails.eval a c6504 := derived6504 a h
  have h5 : Entails.eval a c6500 := derived6500 a h
  have h6 : Entails.eval a c6503 := derived6503 a h
  have h7 : Entails.eval a c4119 := h 4118 (by decide)
  have h8 : Entails.eval a c6505 := derived6505 a h
  have h9 : Entails.eval a c3491 := h 3490 (by decide)
  have h10 : Entails.eval a c5308 := h 5307 (by decide)
  have h11 : Entails.eval a c6306 := derived6306 a h
  have h12 : Entails.eval a c4800 := h 4799 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6507 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨38, by decide⟩, true), (⟨39, by decide⟩, false), (⟨34, by decide⟩, false), (⟨43, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6507 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c5416, some c4119, some c4699, some c3980, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6507 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6507 : lratChecker f6507 p6507 = .success := by decide +kernel
theorem unsat6507 : Unsatisfiable (PosFin 65) f6507 := by
  apply lratCheckerSound f6507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6507
  · intro a ha; simp [p6507] at ha; subst a; trivial
  · exact checked6507
theorem derived6507 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6507 := by
  apply localUnsat_implies_entails f6507 [c6490, c6227, c5416, c4119, c4699, c3980] c6507 unsat6507 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5416 := h 5415 (by decide)
  have h3 : Entails.eval a c4119 := h 4118 (by decide)
  have h4 : Entails.eval a c4699 := h 4698 (by decide)
  have h5 : Entails.eval a c3980 := h 3979 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6508 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6508 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6371, some c6227, some c3978, some c3987, some c3989, some c3974, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6508 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6508 : lratChecker f6508 p6508 = .success := by decide +kernel
theorem unsat6508 : Unsatisfiable (PosFin 65) f6508 := by
  apply lratCheckerSound f6508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6508
  · intro a ha; simp [p6508] at ha; subst a; trivial
  · exact checked6508
theorem derived6508 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6508 := by
  apply localUnsat_implies_entails f6508 [c6490, c6371, c6227, c3978, c3987, c3989, c3974] c6508 unsat6508 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c3978 := h 3977 (by decide)
  have h4 : Entails.eval a c3987 := h 3986 (by decide)
  have h5 : Entails.eval a c3989 := h 3988 (by decide)
  have h6 : Entails.eval a c3974 := h 3973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6509 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6509 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6499, some c6490, some c6227, some c6501, some c6504, some c6506, some c6507, some c6466, some c4121, some c4720, some c4547, some c6508, some c5420, some c5353, some c4367, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6509 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6509 : lratChecker f6509 p6509 = .success := by decide +kernel
theorem unsat6509 : Unsatisfiable (PosFin 65) f6509 := by
  apply lratCheckerSound f6509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6509
  · intro a ha; simp [p6509] at ha; subst a; trivial
  · exact checked6509
theorem derived6509 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6509 := by
  apply localUnsat_implies_entails f6509 [c6499, c6490, c6227, c6501, c6504, c6506, c6507, c6466, c4121, c4720, c4547, c6508, c5420, c5353, c4367] c6509 unsat6509 (by rfl) a
  have h0 : Entails.eval a c6499 := derived6499 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6501 := derived6501 a h
  have h4 : Entails.eval a c6504 := derived6504 a h
  have h5 : Entails.eval a c6506 := derived6506 a h
  have h6 : Entails.eval a c6507 := derived6507 a h
  have h7 : Entails.eval a c6466 := derived6466 a h
  have h8 : Entails.eval a c4121 := h 4120 (by decide)
  have h9 : Entails.eval a c4720 := h 4719 (by decide)
  have h10 : Entails.eval a c4547 := h 4546 (by decide)
  have h11 : Entails.eval a c6508 := derived6508 a h
  have h12 : Entails.eval a c5420 := h 5419 (by decide)
  have h13 : Entails.eval a c5353 := h 5352 (by decide)
  have h14 : Entails.eval a c4367 := h 4366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6510 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨52, by decide⟩, true), (⟨45, by decide⟩, true), (⟨36, by decide⟩, false), (⟨53, by decide⟩, false), (⟨46, by decide⟩, false), (⟨34, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6510 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c4925, some c3435, some c3898, some c3895, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6510 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6510 : lratChecker f6510 p6510 = .success := by decide +kernel
theorem unsat6510 : Unsatisfiable (PosFin 65) f6510 := by
  apply lratCheckerSound f6510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6510
  · intro a ha; simp [p6510] at ha; subst a; trivial
  · exact checked6510
theorem derived6510 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6510 := by
  apply localUnsat_implies_entails f6510 [c6490, c4925, c3435, c3898, c3895] c6510 unsat6510 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c4925 := h 4924 (by decide)
  have h2 : Entails.eval a c3435 := h 3434 (by decide)
  have h3 : Entails.eval a c3898 := h 3897 (by decide)
  have h4 : Entails.eval a c3895 := h 3894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6511 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6511 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6509, some c6499, some c6490, some c6371, some c6227, some c6508, some c5420, some c5407, some c5405, some c5418, some c6510, some c4352, some c4438, some c4432, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6511 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6511 : lratChecker f6511 p6511 = .success := by decide +kernel
theorem unsat6511 : Unsatisfiable (PosFin 65) f6511 := by
  apply lratCheckerSound f6511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6511
  · intro a ha; simp [p6511] at ha; subst a; trivial
  · exact checked6511
theorem derived6511 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6511 := by
  apply localUnsat_implies_entails f6511 [c6509, c6499, c6490, c6371, c6227, c6508, c5420, c5407, c5405, c5418, c6510, c4352, c4438, c4432] c6511 unsat6511 (by rfl) a
  have h0 : Entails.eval a c6509 := derived6509 a h
  have h1 : Entails.eval a c6499 := derived6499 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6371 := derived6371 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6508 := derived6508 a h
  have h6 : Entails.eval a c5420 := h 5419 (by decide)
  have h7 : Entails.eval a c5407 := h 5406 (by decide)
  have h8 : Entails.eval a c5405 := h 5404 (by decide)
  have h9 : Entails.eval a c5418 := h 5417 (by decide)
  have h10 : Entails.eval a c6510 := derived6510 a h
  have h11 : Entails.eval a c4352 := h 4351 (by decide)
  have h12 : Entails.eval a c4438 := h 4437 (by decide)
  have h13 : Entails.eval a c4432 := h 4431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6512 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6512 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6511, some c4728, some c4720, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6512 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6512 : lratChecker f6512 p6512 = .success := by decide +kernel
theorem unsat6512 : Unsatisfiable (PosFin 65) f6512 := by
  apply lratCheckerSound f6512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6512
  · intro a ha; simp [p6512] at ha; subst a; trivial
  · exact checked6512
theorem derived6512 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6512 := by
  apply localUnsat_implies_entails f6512 [c6490, c6227, c6511, c4728, c4720] c6512 unsat6512 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6511 := derived6511 a h
  have h3 : Entails.eval a c4728 := h 4727 (by decide)
  have h4 : Entails.eval a c4720 := h 4719 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6513 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6513 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6509, some c6512, some c6497, some c6490, some c6371, some c6227, some c4868, some c5337, some c4829, some c4823, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6513 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6513 : lratChecker f6513 p6513 = .success := by decide +kernel
theorem unsat6513 : Unsatisfiable (PosFin 65) f6513 := by
  apply lratCheckerSound f6513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6513
  · intro a ha; simp [p6513] at ha; subst a; trivial
  · exact checked6513
theorem derived6513 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6513 := by
  apply localUnsat_implies_entails f6513 [c6509, c6512, c6497, c6490, c6371, c6227, c4868, c5337, c4829, c4823] c6513 unsat6513 (by rfl) a
  have h0 : Entails.eval a c6509 := derived6509 a h
  have h1 : Entails.eval a c6512 := derived6512 a h
  have h2 : Entails.eval a c6497 := derived6497 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6371 := derived6371 a h
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c4868 := h 4867 (by decide)
  have h7 : Entails.eval a c5337 := h 5336 (by decide)
  have h8 : Entails.eval a c4829 := h 4828 (by decide)
  have h9 : Entails.eval a c4823 := h 4822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6514 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6514 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6509, some c6499, some c6490, some c6371, some c6227, some c6512, some c6497, some c6513, some c6508, some c5780, some c5786, some c5787, some c6510, some c5784, some c4352, some c3451, some c5770, some c6198, some c6152, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6514 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked6514 : lratChecker f6514 p6514 = .success := by decide +kernel
theorem unsat6514 : Unsatisfiable (PosFin 65) f6514 := by
  apply lratCheckerSound f6514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6514
  · intro a ha; simp [p6514] at ha; subst a; trivial
  · exact checked6514
theorem derived6514 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6514 := by
  apply localUnsat_implies_entails f6514 [c6509, c6499, c6490, c6371, c6227, c6512, c6497, c6513, c6508, c5780, c5786, c5787, c6510, c5784, c4352, c3451, c5770, c6198, c6152] c6514 unsat6514 (by rfl) a
  have h0 : Entails.eval a c6509 := derived6509 a h
  have h1 : Entails.eval a c6499 := derived6499 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6371 := derived6371 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6512 := derived6512 a h
  have h6 : Entails.eval a c6497 := derived6497 a h
  have h7 : Entails.eval a c6513 := derived6513 a h
  have h8 : Entails.eval a c6508 := derived6508 a h
  have h9 : Entails.eval a c5780 := h 5779 (by decide)
  have h10 : Entails.eval a c5786 := h 5785 (by decide)
  have h11 : Entails.eval a c5787 := h 5786 (by decide)
  have h12 : Entails.eval a c6510 := derived6510 a h
  have h13 : Entails.eval a c5784 := h 5783 (by decide)
  have h14 : Entails.eval a c4352 := h 4351 (by decide)
  have h15 : Entails.eval a c3451 := h 3450 (by decide)
  have h16 : Entails.eval a c5770 := h 5769 (by decide)
  have h17 : Entails.eval a c6198 := derived6198 a h
  have h18 : Entails.eval a c6152 := derived6152 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6515 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6515 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6514, some c6509, some c6490, some c5333, some c6497, some c6499, some c3433, some c4344, some c4885, some c3691, some c3783, some c5780, some c6305, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6515 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6515 : lratChecker f6515 p6515 = .success := by decide +kernel
theorem unsat6515 : Unsatisfiable (PosFin 65) f6515 := by
  apply lratCheckerSound f6515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6515
  · intro a ha; simp [p6515] at ha; subst a; trivial
  · exact checked6515
theorem derived6515 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6515 := by
  apply localUnsat_implies_entails f6515 [c6227, c6514, c6509, c6490, c5333, c6497, c6499, c3433, c4344, c4885, c3691, c3783, c5780, c6305] c6515 unsat6515 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6514 := derived6514 a h
  have h2 : Entails.eval a c6509 := derived6509 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c5333 := h 5332 (by decide)
  have h5 : Entails.eval a c6497 := derived6497 a h
  have h6 : Entails.eval a c6499 := derived6499 a h
  have h7 : Entails.eval a c3433 := h 3432 (by decide)
  have h8 : Entails.eval a c4344 := h 4343 (by decide)
  have h9 : Entails.eval a c4885 := h 4884 (by decide)
  have h10 : Entails.eval a c3691 := h 3690 (by decide)
  have h11 : Entails.eval a c3783 := h 3782 (by decide)
  have h12 : Entails.eval a c5780 := h 5779 (by decide)
  have h13 : Entails.eval a c6305 := derived6305 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6516 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6516 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6514, some c6509, some c6499, some c6490, some c6227, some c5333, some c6515, some c4763, some c4800, some c4119, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6516 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6516 : lratChecker f6516 p6516 = .success := by decide +kernel
theorem unsat6516 : Unsatisfiable (PosFin 65) f6516 := by
  apply lratCheckerSound f6516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6516
  · intro a ha; simp [p6516] at ha; subst a; trivial
  · exact checked6516
theorem derived6516 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6516 := by
  apply localUnsat_implies_entails f6516 [c6514, c6509, c6499, c6490, c6227, c5333, c6515, c4763, c4800, c4119] c6516 unsat6516 (by rfl) a
  have h0 : Entails.eval a c6514 := derived6514 a h
  have h1 : Entails.eval a c6509 := derived6509 a h
  have h2 : Entails.eval a c6499 := derived6499 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c5333 := h 5332 (by decide)
  have h6 : Entails.eval a c6515 := derived6515 a h
  have h7 : Entails.eval a c4763 := h 4762 (by decide)
  have h8 : Entails.eval a c4800 := h 4799 (by decide)
  have h9 : Entails.eval a c4119 := h 4118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6517 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6517 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6499, some c6514, some c6516, some c5416, some c4719, some c3980, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6517 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6517 : lratChecker f6517 p6517 = .success := by decide +kernel
theorem unsat6517 : Unsatisfiable (PosFin 65) f6517 := by
  apply lratCheckerSound f6517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6517
  · intro a ha; simp [p6517] at ha; subst a; trivial
  · exact checked6517
theorem derived6517 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6517 := by
  apply localUnsat_implies_entails f6517 [c6490, c6227, c6499, c6514, c6516, c5416, c4719, c3980] c6517 unsat6517 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6499 := derived6499 a h
  have h3 : Entails.eval a c6514 := derived6514 a h
  have h4 : Entails.eval a c6516 := derived6516 a h
  have h5 : Entails.eval a c5416 := h 5415 (by decide)
  have h6 : Entails.eval a c4719 := h 4718 (by decide)
  have h7 : Entails.eval a c3980 := h 3979 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6518 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6518 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6369, some c3671, some c3648, some c4612, some c3959, some c4421, some c4222, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6518 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6518 : lratChecker f6518 p6518 = .success := by decide +kernel
theorem unsat6518 : Unsatisfiable (PosFin 65) f6518 := by
  apply lratCheckerSound f6518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6518
  · intro a ha; simp [p6518] at ha; subst a; trivial
  · exact checked6518
theorem derived6518 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6518 := by
  apply localUnsat_implies_entails f6518 [c6490, c6227, c6369, c3671, c3648, c4612, c3959, c4421, c4222] c6518 unsat6518 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6369 := derived6369 a h
  have h3 : Entails.eval a c3671 := h 3670 (by decide)
  have h4 : Entails.eval a c3648 := h 3647 (by decide)
  have h5 : Entails.eval a c4612 := h 4611 (by decide)
  have h6 : Entails.eval a c3959 := h 3958 (by decide)
  have h7 : Entails.eval a c4421 := h 4420 (by decide)
  have h8 : Entails.eval a c4222 := h 4221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6519 : DefaultClause 65 := directClause [(⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6519 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6508, some c4290, some c4222, some c4843, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6519 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6519 : lratChecker f6519 p6519 = .success := by decide +kernel
theorem unsat6519 : Unsatisfiable (PosFin 65) f6519 := by
  apply lratCheckerSound f6519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6519
  · intro a ha; simp [p6519] at ha; subst a; trivial
  · exact checked6519
theorem derived6519 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6519 := by
  apply localUnsat_implies_entails f6519 [c6490, c6227, c6508, c4290, c4222, c4843] c6519 unsat6519 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6508 := derived6508 a h
  have h3 : Entails.eval a c4290 := h 4289 (by decide)
  have h4 : Entails.eval a c4222 := h 4221 (by decide)
  have h5 : Entails.eval a c4843 := h 4842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6520 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6520 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c4843, some c4800, some c5680, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6520 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6520 : lratChecker f6520 p6520 = .success := by decide +kernel
theorem unsat6520 : Unsatisfiable (PosFin 65) f6520 := by
  apply lratCheckerSound f6520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6520
  · intro a ha; simp [p6520] at ha; subst a; trivial
  · exact checked6520
theorem derived6520 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6520 := by
  apply localUnsat_implies_entails f6520 [c6490, c6227, c4843, c4800, c5680] c6520 unsat6520 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4843 := h 4842 (by decide)
  have h3 : Entails.eval a c4800 := h 4799 (by decide)
  have h4 : Entails.eval a c5680 := h 5679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6521 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6521 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6517, some c6518, some c6490, some c6227, some c6369, some c6519, some c3710, some c4119, some c6520, some c6306, some c6497, some c5333, some c4344, some c3783, some c6305, some c5286, some c5801, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6521 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked6521 : lratChecker f6521 p6521 = .success := by decide +kernel
theorem unsat6521 : Unsatisfiable (PosFin 65) f6521 := by
  apply lratCheckerSound f6521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6521
  · intro a ha; simp [p6521] at ha; subst a; trivial
  · exact checked6521
theorem derived6521 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6521 := by
  apply localUnsat_implies_entails f6521 [c6517, c6518, c6490, c6227, c6369, c6519, c3710, c4119, c6520, c6306, c6497, c5333, c4344, c3783, c6305, c5286, c5801] c6521 unsat6521 (by rfl) a
  have h0 : Entails.eval a c6517 := derived6517 a h
  have h1 : Entails.eval a c6518 := derived6518 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6369 := derived6369 a h
  have h5 : Entails.eval a c6519 := derived6519 a h
  have h6 : Entails.eval a c3710 := h 3709 (by decide)
  have h7 : Entails.eval a c4119 := h 4118 (by decide)
  have h8 : Entails.eval a c6520 := derived6520 a h
  have h9 : Entails.eval a c6306 := derived6306 a h
  have h10 : Entails.eval a c6497 := derived6497 a h
  have h11 : Entails.eval a c5333 := h 5332 (by decide)
  have h12 : Entails.eval a c4344 := h 4343 (by decide)
  have h13 : Entails.eval a c3783 := h 3782 (by decide)
  have h14 : Entails.eval a c6305 := derived6305 a h
  have h15 : Entails.eval a c5286 := h 5285 (by decide)
  have h16 : Entails.eval a c5801 := h 5800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6522 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨64, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6522 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6500, some c6497, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p6522 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6522 : lratChecker f6522 p6522 = .success := by decide +kernel
theorem unsat6522 : Unsatisfiable (PosFin 65) f6522 := by
  apply lratCheckerSound f6522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6522
  · intro a ha; simp [p6522] at ha; subst a; trivial
  · exact checked6522
theorem derived6522 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6522 := by
  apply localUnsat_implies_entails f6522 [c6500, c6497] c6522 unsat6522 (by rfl) a
  have h0 : Entails.eval a c6500 := derived6500 a h
  have h1 : Entails.eval a c6497 := derived6497 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6523 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6523 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6521, some c6517, some c6518, some c6490, some c6227, some c6369, some c6492, some c6232, some c6522, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6523 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6523 : lratChecker f6523 p6523 = .success := by decide +kernel
theorem unsat6523 : Unsatisfiable (PosFin 65) f6523 := by
  apply lratCheckerSound f6523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6523
  · intro a ha; simp [p6523] at ha; subst a; trivial
  · exact checked6523
theorem derived6523 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6523 := by
  apply localUnsat_implies_entails f6523 [c6521, c6517, c6518, c6490, c6227, c6369, c6492, c6232, c6522] c6523 unsat6523 (by rfl) a
  have h0 : Entails.eval a c6521 := derived6521 a h
  have h1 : Entails.eval a c6517 := derived6517 a h
  have h2 : Entails.eval a c6518 := derived6518 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6369 := derived6369 a h
  have h6 : Entails.eval a c6492 := derived6492 a h
  have h7 : Entails.eval a c6232 := derived6232 a h
  have h8 : Entails.eval a c6522 := derived6522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6524 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6524 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6517, some c6490, some c6227, some c6369, some c6518, some c6521, some c6523, some c5333, some c5308, some c4484, some c6287, some c6270, some c6505, some c6272, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6524 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked6524 : lratChecker f6524 p6524 = .success := by decide +kernel
theorem unsat6524 : Unsatisfiable (PosFin 65) f6524 := by
  apply lratCheckerSound f6524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6524
  · intro a ha; simp [p6524] at ha; subst a; trivial
  · exact checked6524
theorem derived6524 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6524 := by
  apply localUnsat_implies_entails f6524 [c6517, c6490, c6227, c6369, c6518, c6521, c6523, c5333, c5308, c4484, c6287, c6270, c6505, c6272] c6524 unsat6524 (by rfl) a
  have h0 : Entails.eval a c6517 := derived6517 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6369 := derived6369 a h
  have h4 : Entails.eval a c6518 := derived6518 a h
  have h5 : Entails.eval a c6521 := derived6521 a h
  have h6 : Entails.eval a c6523 := derived6523 a h
  have h7 : Entails.eval a c5333 := h 5332 (by decide)
  have h8 : Entails.eval a c5308 := h 5307 (by decide)
  have h9 : Entails.eval a c4484 := h 4483 (by decide)
  have h10 : Entails.eval a c6287 := derived6287 a h
  have h11 : Entails.eval a c6270 := derived6270 a h
  have h12 : Entails.eval a c6505 := derived6505 a h
  have h13 : Entails.eval a c6272 := derived6272 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6525 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨42, by decide⟩, true), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6525 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6492, some c6524, some c6517, some c6490, some c6227, some c6304, some c5681, some c5918, some c4524, some c6270, some c6272, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6525 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6525 : lratChecker f6525 p6525 = .success := by decide +kernel
theorem unsat6525 : Unsatisfiable (PosFin 65) f6525 := by
  apply lratCheckerSound f6525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6525
  · intro a ha; simp [p6525] at ha; subst a; trivial
  · exact checked6525
theorem derived6525 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6525 := by
  apply localUnsat_implies_entails f6525 [c6492, c6524, c6517, c6490, c6227, c6304, c5681, c5918, c4524, c6270, c6272] c6525 unsat6525 (by rfl) a
  have h0 : Entails.eval a c6492 := derived6492 a h
  have h1 : Entails.eval a c6524 := derived6524 a h
  have h2 : Entails.eval a c6517 := derived6517 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6304 := derived6304 a h
  have h6 : Entails.eval a c5681 := h 5680 (by decide)
  have h7 : Entails.eval a c5918 := derived5918 a h
  have h8 : Entails.eval a c4524 := h 4523 (by decide)
  have h9 : Entails.eval a c6270 := derived6270 a h
  have h10 : Entails.eval a c6272 := derived6272 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6526 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6526 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c5334, some c5337, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6526 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6526 : lratChecker f6526 p6526 = .success := by decide +kernel
theorem unsat6526 : Unsatisfiable (PosFin 65) f6526 := by
  apply lratCheckerSound f6526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6526
  · intro a ha; simp [p6526] at ha; subst a; trivial
  · exact checked6526
theorem derived6526 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6526 := by
  apply localUnsat_implies_entails f6526 [c6490, c6227, c5334, c5337] c6526 unsat6526 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c5334 := h 5333 (by decide)
  have h3 : Entails.eval a c5337 := h 5336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6527 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6527 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c3848, some c4491, some c5684, some c4529, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6527 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6527 : lratChecker f6527 p6527 = .success := by decide +kernel
theorem unsat6527 : Unsatisfiable (PosFin 65) f6527 := by
  apply lratCheckerSound f6527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6527
  · intro a ha; simp [p6527] at ha; subst a; trivial
  · exact checked6527
theorem derived6527 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6527 := by
  apply localUnsat_implies_entails f6527 [c6490, c6227, c3848, c4491, c5684, c4529] c6527 unsat6527 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c3848 := h 3847 (by decide)
  have h3 : Entails.eval a c4491 := h 4490 (by decide)
  have h4 : Entails.eval a c5684 := h 5683 (by decide)
  have h5 : Entails.eval a c4529 := h 4528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6528 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6528 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6522, some c6524, some c6517, some c6492, some c6526, some c6525, some c6527, some c5681, some c6402, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6528 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6528 : lratChecker f6528 p6528 = .success := by decide +kernel
theorem unsat6528 : Unsatisfiable (PosFin 65) f6528 := by
  apply lratCheckerSound f6528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6528
  · intro a ha; simp [p6528] at ha; subst a; trivial
  · exact checked6528
theorem derived6528 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6528 := by
  apply localUnsat_implies_entails f6528 [c6522, c6524, c6517, c6492, c6526, c6525, c6527, c5681, c6402] c6528 unsat6528 (by rfl) a
  have h0 : Entails.eval a c6522 := derived6522 a h
  have h1 : Entails.eval a c6524 := derived6524 a h
  have h2 : Entails.eval a c6517 := derived6517 a h
  have h3 : Entails.eval a c6492 := derived6492 a h
  have h4 : Entails.eval a c6526 := derived6526 a h
  have h5 : Entails.eval a c6525 := derived6525 a h
  have h6 : Entails.eval a c6527 := derived6527 a h
  have h7 : Entails.eval a c5681 := h 5680 (by decide)
  have h8 : Entails.eval a c6402 := derived6402 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6529 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6529 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6528, some c6524, some c6517, some c6526, some c6504, some c5681, some c4121, some c4485, some c4524, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6529 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6529 : lratChecker f6529 p6529 = .success := by decide +kernel
theorem unsat6529 : Unsatisfiable (PosFin 65) f6529 := by
  apply lratCheckerSound f6529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6529
  · intro a ha; simp [p6529] at ha; subst a; trivial
  · exact checked6529
theorem derived6529 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6529 := by
  apply localUnsat_implies_entails f6529 [c6528, c6524, c6517, c6526, c6504, c5681, c4121, c4485, c4524] c6529 unsat6529 (by rfl) a
  have h0 : Entails.eval a c6528 := derived6528 a h
  have h1 : Entails.eval a c6524 := derived6524 a h
  have h2 : Entails.eval a c6517 := derived6517 a h
  have h3 : Entails.eval a c6526 := derived6526 a h
  have h4 : Entails.eval a c6504 := derived6504 a h
  have h5 : Entails.eval a c5681 := h 5680 (by decide)
  have h6 : Entails.eval a c4121 := h 4120 (by decide)
  have h7 : Entails.eval a c4485 := h 4484 (by decide)
  have h8 : Entails.eval a c4524 := h 4523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6530 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨40, by decide⟩, true), (⟨42, by decide⟩, true), (⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6530 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5293, some c5664, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6530 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6530 : lratChecker f6530 p6530 = .success := by decide +kernel
theorem unsat6530 : Unsatisfiable (PosFin 65) f6530 := by
  apply lratCheckerSound f6530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6530
  · intro a ha; simp [p6530] at ha; subst a; trivial
  · exact checked6530
theorem derived6530 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6530 := by
  apply localUnsat_implies_entails f6530 [c5293, c5664] c6530 unsat6530 (by rfl) a
  have h0 : Entails.eval a c5293 := h 5292 (by decide)
  have h1 : Entails.eval a c5664 := h 5663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6531 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6531 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6524, some c6490, some c6371, some c6227, some c6522, some c6528, some c6529, some c6530, some c6302, some c4128, some c4808, some c3451, some c6424, some c6133, some c5292, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6531 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6531 : lratChecker f6531 p6531 = .success := by decide +kernel
theorem unsat6531 : Unsatisfiable (PosFin 65) f6531 := by
  apply lratCheckerSound f6531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6531
  · intro a ha; simp [p6531] at ha; subst a; trivial
  · exact checked6531
theorem derived6531 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6531 := by
  apply localUnsat_implies_entails f6531 [c6524, c6490, c6371, c6227, c6522, c6528, c6529, c6530, c6302, c4128, c4808, c3451, c6424, c6133, c5292] c6531 unsat6531 (by rfl) a
  have h0 : Entails.eval a c6524 := derived6524 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6522 := derived6522 a h
  have h5 : Entails.eval a c6528 := derived6528 a h
  have h6 : Entails.eval a c6529 := derived6529 a h
  have h7 : Entails.eval a c6530 := derived6530 a h
  have h8 : Entails.eval a c6302 := derived6302 a h
  have h9 : Entails.eval a c4128 := h 4127 (by decide)
  have h10 : Entails.eval a c4808 := h 4807 (by decide)
  have h11 : Entails.eval a c3451 := h 3450 (by decide)
  have h12 : Entails.eval a c6424 := derived6424 a h
  have h13 : Entails.eval a c6133 := derived6133 a h
  have h14 : Entails.eval a c5292 := h 5291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6532 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨39, by decide⟩, false), (⟨43, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6532 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c4128, some c5358, some c4423, some c4620, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6532 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6532 : lratChecker f6532 p6532 = .success := by decide +kernel
theorem unsat6532 : Unsatisfiable (PosFin 65) f6532 := by
  apply lratCheckerSound f6532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6532
  · intro a ha; simp [p6532] at ha; subst a; trivial
  · exact checked6532
theorem derived6532 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6532 := by
  apply localUnsat_implies_entails f6532 [c6490, c6227, c4128, c5358, c4423, c4620] c6532 unsat6532 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c4128 := h 4127 (by decide)
  have h3 : Entails.eval a c5358 := h 5357 (by decide)
  have h4 : Entails.eval a c4423 := h 4422 (by decide)
  have h5 : Entails.eval a c4620 := h 4619 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6533 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6533 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6531, some c6524, some c6517, some c6532, some c4121, some c4143, some c5615, some c5681, some c4485, some c4524, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6533 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6533 : lratChecker f6533 p6533 = .success := by decide +kernel
theorem unsat6533 : Unsatisfiable (PosFin 65) f6533 := by
  apply lratCheckerSound f6533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6533
  · intro a ha; simp [p6533] at ha; subst a; trivial
  · exact checked6533
theorem derived6533 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6533 := by
  apply localUnsat_implies_entails f6533 [c6531, c6524, c6517, c6532, c4121, c4143, c5615, c5681, c4485, c4524] c6533 unsat6533 (by rfl) a
  have h0 : Entails.eval a c6531 := derived6531 a h
  have h1 : Entails.eval a c6524 := derived6524 a h
  have h2 : Entails.eval a c6517 := derived6517 a h
  have h3 : Entails.eval a c6532 := derived6532 a h
  have h4 : Entails.eval a c4121 := h 4120 (by decide)
  have h5 : Entails.eval a c4143 := h 4142 (by decide)
  have h6 : Entails.eval a c5615 := h 5614 (by decide)
  have h7 : Entails.eval a c5681 := h 5680 (by decide)
  have h8 : Entails.eval a c4485 := h 4484 (by decide)
  have h9 : Entails.eval a c4524 := h 4523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6534 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6534 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6533, some c6531, some c6524, some c6517, some c6490, some c3961, some c3570, some c4485, some c3751, some c6492, some c6301, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6534 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6534 : lratChecker f6534 p6534 = .success := by decide +kernel
theorem unsat6534 : Unsatisfiable (PosFin 65) f6534 := by
  apply lratCheckerSound f6534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6534
  · intro a ha; simp [p6534] at ha; subst a; trivial
  · exact checked6534
theorem derived6534 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6534 := by
  apply localUnsat_implies_entails f6534 [c6533, c6531, c6524, c6517, c6490, c3961, c3570, c4485, c3751, c6492, c6301] c6534 unsat6534 (by rfl) a
  have h0 : Entails.eval a c6533 := derived6533 a h
  have h1 : Entails.eval a c6531 := derived6531 a h
  have h2 : Entails.eval a c6524 := derived6524 a h
  have h3 : Entails.eval a c6517 := derived6517 a h
  have h4 : Entails.eval a c6490 := derived6490 a h
  have h5 : Entails.eval a c3961 := h 3960 (by decide)
  have h6 : Entails.eval a c3570 := h 3569 (by decide)
  have h7 : Entails.eval a c4485 := h 4484 (by decide)
  have h8 : Entails.eval a c3751 := h 3750 (by decide)
  have h9 : Entails.eval a c6492 := derived6492 a h
  have h10 : Entails.eval a c6301 := derived6301 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6535 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6535 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6517, some c6490, some c6227, some c6531, some c6533, some c6534, some c3966, some c4105, some c4620, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6535 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6535 : lratChecker f6535 p6535 = .success := by decide +kernel
theorem unsat6535 : Unsatisfiable (PosFin 65) f6535 := by
  apply lratCheckerSound f6535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6535
  · intro a ha; simp [p6535] at ha; subst a; trivial
  · exact checked6535
theorem derived6535 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6535 := by
  apply localUnsat_implies_entails f6535 [c6517, c6490, c6227, c6531, c6533, c6534, c3966, c4105, c4620] c6535 unsat6535 (by rfl) a
  have h0 : Entails.eval a c6517 := derived6517 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6531 := derived6531 a h
  have h4 : Entails.eval a c6533 := derived6533 a h
  have h5 : Entails.eval a c6534 := derived6534 a h
  have h6 : Entails.eval a c3966 := h 3965 (by decide)
  have h7 : Entails.eval a c4105 := h 4104 (by decide)
  have h8 : Entails.eval a c4620 := h 4619 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6536 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨61, by decide⟩, true), (⟨63, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6536 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3578, some c4620, some c4491, some c3795, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p6536 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6536 : lratChecker f6536 p6536 = .success := by decide +kernel
theorem unsat6536 : Unsatisfiable (PosFin 65) f6536 := by
  apply lratCheckerSound f6536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6536
  · intro a ha; simp [p6536] at ha; subst a; trivial
  · exact checked6536
theorem derived6536 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6536 := by
  apply localUnsat_implies_entails f6536 [c3578, c4620, c4491, c3795] c6536 unsat6536 (by rfl) a
  have h0 : Entails.eval a c3578 := h 3577 (by decide)
  have h1 : Entails.eval a c4620 := h 4619 (by decide)
  have h2 : Entails.eval a c4491 := h 4490 (by decide)
  have h3 : Entails.eval a c3795 := h 3794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6537 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨61, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6537 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3881, some c6423, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6537 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6537 : lratChecker f6537 p6537 = .success := by decide +kernel
theorem unsat6537 : Unsatisfiable (PosFin 65) f6537 := by
  apply lratCheckerSound f6537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6537
  · intro a ha; simp [p6537] at ha; subst a; trivial
  · exact checked6537
theorem derived6537 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6537 := by
  apply localUnsat_implies_entails f6537 [c3881, c6423] c6537 unsat6537 (by rfl) a
  have h0 : Entails.eval a c3881 := h 3880 (by decide)
  have h1 : Entails.eval a c6423 := derived6423 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6538 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨61, by decide⟩, false), (⟨64, by decide⟩, false), (⟨39, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6538 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4777, some c5566, some c4450, some c4346, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p6538 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6538 : lratChecker f6538 p6538 = .success := by decide +kernel
theorem unsat6538 : Unsatisfiable (PosFin 65) f6538 := by
  apply lratCheckerSound f6538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6538
  · intro a ha; simp [p6538] at ha; subst a; trivial
  · exact checked6538
theorem derived6538 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6538 := by
  apply localUnsat_implies_entails f6538 [c4777, c5566, c4450, c4346] c6538 unsat6538 (by rfl) a
  have h0 : Entails.eval a c4777 := h 4776 (by decide)
  have h1 : Entails.eval a c5566 := h 5565 (by decide)
  have h2 : Entails.eval a c4450 := h 4449 (by decide)
  have h3 : Entails.eval a c4346 := h 4345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6539 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6539 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6535, some c6524, some c6517, some c6537, some c6538, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6539 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6539 : lratChecker f6539 p6539 = .success := by decide +kernel
theorem unsat6539 : Unsatisfiable (PosFin 65) f6539 := by
  apply lratCheckerSound f6539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6539
  · intro a ha; simp [p6539] at ha; subst a; trivial
  · exact checked6539
theorem derived6539 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6539 := by
  apply localUnsat_implies_entails f6539 [c6535, c6524, c6517, c6537, c6538] c6539 unsat6539 (by rfl) a
  have h0 : Entails.eval a c6535 := derived6535 a h
  have h1 : Entails.eval a c6524 := derived6524 a h
  have h2 : Entails.eval a c6517 := derived6517 a h
  have h3 : Entails.eval a c6537 := derived6537 a h
  have h4 : Entails.eval a c6538 := derived6538 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6540 : DefaultClause 65 := directClause [(⟨51, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6540 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6490, some c6227, some c6517, some c6535, some c6539, some c6536, some c4455, some c3886, some c5684, some c3699, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6540 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked6540 : lratChecker f6540 p6540 = .success := by decide +kernel
theorem unsat6540 : Unsatisfiable (PosFin 65) f6540 := by
  apply lratCheckerSound f6540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6540
  · intro a ha; simp [p6540] at ha; subst a; trivial
  · exact checked6540
theorem derived6540 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6540 := by
  apply localUnsat_implies_entails f6540 [c6490, c6227, c6517, c6535, c6539, c6536, c4455, c3886, c5684, c3699] c6540 unsat6540 (by rfl) a
  have h0 : Entails.eval a c6490 := derived6490 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6517 := derived6517 a h
  have h3 : Entails.eval a c6535 := derived6535 a h
  have h4 : Entails.eval a c6539 := derived6539 a h
  have h5 : Entails.eval a c6536 := derived6536 a h
  have h6 : Entails.eval a c4455 := h 4454 (by decide)
  have h7 : Entails.eval a c3886 := h 3885 (by decide)
  have h8 : Entails.eval a c5684 := h 5683 (by decide)
  have h9 : Entails.eval a c3699 := h 3698 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6541 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6541 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6490, some c6371, some c6227, some c3886, some c5817, some c5678, some c3739, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6541 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6541 : lratChecker f6541 p6541 = .success := by decide +kernel
theorem unsat6541 : Unsatisfiable (PosFin 65) f6541 := by
  apply lratCheckerSound f6541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6541
  · intro a ha; simp [p6541] at ha; subst a; trivial
  · exact checked6541
theorem derived6541 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6541 := by
  apply localUnsat_implies_entails f6541 [c6540, c6490, c6371, c6227, c3886, c5817, c5678, c3739] c6541 unsat6541 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c3886 := h 3885 (by decide)
  have h5 : Entails.eval a c5817 := h 5816 (by decide)
  have h6 : Entails.eval a c5678 := h 5677 (by decide)
  have h7 : Entails.eval a c3739 := h 3738 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6542 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨42, by decide⟩, true), (⟨57, by decide⟩, false), (⟨34, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨36, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6542 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3981, some c5807, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6542 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6542 : lratChecker f6542 p6542 = .success := by decide +kernel
theorem unsat6542 : Unsatisfiable (PosFin 65) f6542 := by
  apply lratCheckerSound f6542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6542
  · intro a ha; simp [p6542] at ha; subst a; trivial
  · exact checked6542
theorem derived6542 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6542 := by
  apply localUnsat_implies_entails f6542 [c3981, c5807] c6542 unsat6542 (by rfl) a
  have h0 : Entails.eval a c3981 := h 3980 (by decide)
  have h1 : Entails.eval a c5807 := h 5806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6543 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false), (⟨45, by decide⟩, true), (⟨59, by decide⟩, true), (⟨38, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨61, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6543 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3194, some c3241, some c2870, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p6543 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6543 : lratChecker f6543 p6543 = .success := by decide +kernel
theorem unsat6543 : Unsatisfiable (PosFin 65) f6543 := by
  apply lratCheckerSound f6543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6543
  · intro a ha; simp [p6543] at ha; subst a; trivial
  · exact checked6543
theorem derived6543 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6543 := by
  apply localUnsat_implies_entails f6543 [c3194, c3241, c2870] c6543 unsat6543 (by rfl) a
  have h0 : Entails.eval a c3194 := h 3193 (by decide)
  have h1 : Entails.eval a c3241 := h 3240 (by decide)
  have h2 : Entails.eval a c2870 := h 2869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6544 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨34, by decide⟩, false), (⟨48, by decide⟩, false), (⟨35, by decide⟩, true), (⟨47, by decide⟩, true), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6544 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2699, some c2729, some c3132, some c2736, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6544 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6544 : lratChecker f6544 p6544 = .success := by decide +kernel
theorem unsat6544 : Unsatisfiable (PosFin 65) f6544 := by
  apply lratCheckerSound f6544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6544
  · intro a ha; simp [p6544] at ha; subst a; trivial
  · exact checked6544
theorem derived6544 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6544 := by
  apply localUnsat_implies_entails f6544 [c2699, c2729, c3132, c2736] c6544 unsat6544 (by rfl) a
  have h0 : Entails.eval a c2699 := h 2698 (by decide)
  have h1 : Entails.eval a c2729 := h 2728 (by decide)
  have h2 : Entails.eval a c3132 := h 3131 (by decide)
  have h3 : Entails.eval a c2736 := h 2735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6545 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨52, by decide⟩, false), (⟨34, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6545 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2994, some c2912, some c2980, some c3172, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p6545 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6545 : lratChecker f6545 p6545 = .success := by decide +kernel
theorem unsat6545 : Unsatisfiable (PosFin 65) f6545 := by
  apply lratCheckerSound f6545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6545
  · intro a ha; simp [p6545] at ha; subst a; trivial
  · exact checked6545
theorem derived6545 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6545 := by
  apply localUnsat_implies_entails f6545 [c2994, c2912, c2980, c3172] c6545 unsat6545 (by rfl) a
  have h0 : Entails.eval a c2994 := h 2993 (by decide)
  have h1 : Entails.eval a c2912 := h 2911 (by decide)
  have h2 : Entails.eval a c2980 := h 2979 (by decide)
  have h3 : Entails.eval a c3172 := h 3171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6546 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨45, by decide⟩, true), (⟨57, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, false), (⟨33, by decide⟩, true), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6546 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6371, some c3202, some c3252, some c2871, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6546 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6546 : lratChecker f6546 p6546 = .success := by decide +kernel
theorem unsat6546 : Unsatisfiable (PosFin 65) f6546 := by
  apply lratCheckerSound f6546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6546
  · intro a ha; simp [p6546] at ha; subst a; trivial
  · exact checked6546
theorem derived6546 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6546 := by
  apply localUnsat_implies_entails f6546 [c6540, c6371, c3202, c3252, c2871] c6546 unsat6546 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c3202 := h 3201 (by decide)
  have h3 : Entails.eval a c3252 := h 3251 (by decide)
  have h4 : Entails.eval a c2871 := h 2870 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6547 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6547 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6371, some c6227, some c6490, some c6541, some c5549, some c6540, some c6449, some c5326, some c4772, some c4920, some c6285, some c6494, some c6456, some c4352, some c4423, some c5728, some c6542, some c6173, some c3610, some c5938, some c6451, some c5420, some c3709, some c4428, some c5393, some c6544, some c6543, some c6545, some c6546, some c2703, some c2777, some c3337, some c3043, some c3063, some c2971, some c90, some c86, some c95, some c992, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6547 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]]
theorem checked6547 : lratChecker f6547 p6547 = .success := by decide +kernel
theorem unsat6547 : Unsatisfiable (PosFin 65) f6547 := by
  apply lratCheckerSound f6547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6547
  · intro a ha; simp [p6547] at ha; subst a; trivial
  · exact checked6547
theorem derived6547 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6547 := by
  apply localUnsat_implies_entails f6547 [c6371, c6227, c6490, c6541, c5549, c6540, c6449, c5326, c4772, c4920, c6285, c6494, c6456, c4352, c4423, c5728, c6542, c6173, c3610, c5938, c6451, c5420, c3709, c4428, c5393, c6544, c6543, c6545, c6546, c2703, c2777, c3337, c3043, c3063, c2971, c90, c86, c95, c992] c6547 unsat6547 (by rfl) a
  have h0 : Entails.eval a c6371 := derived6371 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6541 := derived6541 a h
  have h4 : Entails.eval a c5549 := h 5548 (by decide)
  have h5 : Entails.eval a c6540 := derived6540 a h
  have h6 : Entails.eval a c6449 := derived6449 a h
  have h7 : Entails.eval a c5326 := h 5325 (by decide)
  have h8 : Entails.eval a c4772 := h 4771 (by decide)
  have h9 : Entails.eval a c4920 := h 4919 (by decide)
  have h10 : Entails.eval a c6285 := derived6285 a h
  have h11 : Entails.eval a c6494 := derived6494 a h
  have h12 : Entails.eval a c6456 := derived6456 a h
  have h13 : Entails.eval a c4352 := h 4351 (by decide)
  have h14 : Entails.eval a c4423 := h 4422 (by decide)
  have h15 : Entails.eval a c5728 := h 5727 (by decide)
  have h16 : Entails.eval a c6542 := derived6542 a h
  have h17 : Entails.eval a c6173 := derived6173 a h
  have h18 : Entails.eval a c3610 := h 3609 (by decide)
  have h19 : Entails.eval a c5938 := derived5938 a h
  have h20 : Entails.eval a c6451 := derived6451 a h
  have h21 : Entails.eval a c5420 := h 5419 (by decide)
  have h22 : Entails.eval a c3709 := h 3708 (by decide)
  have h23 : Entails.eval a c4428 := h 4427 (by decide)
  have h24 : Entails.eval a c5393 := h 5392 (by decide)
  have h25 : Entails.eval a c6544 := derived6544 a h
  have h26 : Entails.eval a c6543 := derived6543 a h
  have h27 : Entails.eval a c6545 := derived6545 a h
  have h28 : Entails.eval a c6546 := derived6546 a h
  have h29 : Entails.eval a c2703 := h 2702 (by decide)
  have h30 : Entails.eval a c2777 := h 2776 (by decide)
  have h31 : Entails.eval a c3337 := h 3336 (by decide)
  have h32 : Entails.eval a c3043 := h 3042 (by decide)
  have h33 : Entails.eval a c3063 := h 3062 (by decide)
  have h34 : Entails.eval a c2971 := h 2970 (by decide)
  have h35 : Entails.eval a c90 := h 89 (by decide)
  have h36 : Entails.eval a c86 := h 85 (by decide)
  have h37 : Entails.eval a c95 := h 94 (by decide)
  have h38 : Entails.eval a c992 := h 991 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6548 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨45, by decide⟩, false), (⟨52, by decide⟩, false), (⟨41, by decide⟩, false), (⟨57, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6548 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5686, some c2703, some c2777, some c3080, some c3229, some c3210, some c3352, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p6548 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6548 : lratChecker f6548 p6548 = .success := by decide +kernel
theorem unsat6548 : Unsatisfiable (PosFin 65) f6548 := by
  apply lratCheckerSound f6548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6548
  · intro a ha; simp [p6548] at ha; subst a; trivial
  · exact checked6548
theorem derived6548 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6548 := by
  apply localUnsat_implies_entails f6548 [c5686, c2703, c2777, c3080, c3229, c3210, c3352] c6548 unsat6548 (by rfl) a
  have h0 : Entails.eval a c5686 := h 5685 (by decide)
  have h1 : Entails.eval a c2703 := h 2702 (by decide)
  have h2 : Entails.eval a c2777 := h 2776 (by decide)
  have h3 : Entails.eval a c3080 := h 3079 (by decide)
  have h4 : Entails.eval a c3229 := h 3228 (by decide)
  have h5 : Entails.eval a c3210 := h 3209 (by decide)
  have h6 : Entails.eval a c3352 := h 3351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6549 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6549 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6371, some c6227, some c6490, some c6541, some c4772, some c5549, some c6547, some c4880, some c4920, some c3610, some c6449, some c6451, some c6494, some c3989, some c5248, some c6285, some c5326, some c6456, some c4352, some c4423, some c5728, some c6542, some c4877, some c5938, some c6548, some c3202, some c3252, some c2872, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6549 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked6549 : lratChecker f6549 p6549 = .success := by decide +kernel
theorem unsat6549 : Unsatisfiable (PosFin 65) f6549 := by
  apply lratCheckerSound f6549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6549
  · intro a ha; simp [p6549] at ha; subst a; trivial
  · exact checked6549
theorem derived6549 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6549 := by
  apply localUnsat_implies_entails f6549 [c6540, c6371, c6227, c6490, c6541, c4772, c5549, c6547, c4880, c4920, c3610, c6449, c6451, c6494, c3989, c5248, c6285, c5326, c6456, c4352, c4423, c5728, c6542, c4877, c5938, c6548, c3202, c3252, c2872] c6549 unsat6549 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6371 := derived6371 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6541 := derived6541 a h
  have h5 : Entails.eval a c4772 := h 4771 (by decide)
  have h6 : Entails.eval a c5549 := h 5548 (by decide)
  have h7 : Entails.eval a c6547 := derived6547 a h
  have h8 : Entails.eval a c4880 := h 4879 (by decide)
  have h9 : Entails.eval a c4920 := h 4919 (by decide)
  have h10 : Entails.eval a c3610 := h 3609 (by decide)
  have h11 : Entails.eval a c6449 := derived6449 a h
  have h12 : Entails.eval a c6451 := derived6451 a h
  have h13 : Entails.eval a c6494 := derived6494 a h
  have h14 : Entails.eval a c3989 := h 3988 (by decide)
  have h15 : Entails.eval a c5248 := h 5247 (by decide)
  have h16 : Entails.eval a c6285 := derived6285 a h
  have h17 : Entails.eval a c5326 := h 5325 (by decide)
  have h18 : Entails.eval a c6456 := derived6456 a h
  have h19 : Entails.eval a c4352 := h 4351 (by decide)
  have h20 : Entails.eval a c4423 := h 4422 (by decide)
  have h21 : Entails.eval a c5728 := h 5727 (by decide)
  have h22 : Entails.eval a c6542 := derived6542 a h
  have h23 : Entails.eval a c4877 := h 4876 (by decide)
  have h24 : Entails.eval a c5938 := derived5938 a h
  have h25 : Entails.eval a c6548 := derived6548 a h
  have h26 : Entails.eval a c3202 := h 3201 (by decide)
  have h27 : Entails.eval a c3252 := h 3251 (by decide)
  have h28 : Entails.eval a c2872 := h 2871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6550 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6550 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6227, some c6490, some c6541, some c4772, some c5549, some c4352, some c6371, some c6540, some c4920, some c6449, some c6285, some c3610, some c6451, some c5326, some c6494, some c6456, some c4423, some c5728, some c6542, some c6547, some c4880, some c3989, some c4877, some c5248, some c5686, some c6549, some c2699, some c2729, some c2736, some c3133, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6550 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked6550 : lratChecker f6550 p6550 = .success := by decide +kernel
theorem unsat6550 : Unsatisfiable (PosFin 65) f6550 := by
  apply lratCheckerSound f6550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6550
  · intro a ha; simp [p6550] at ha; subst a; trivial
  · exact checked6550
theorem derived6550 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6550 := by
  apply localUnsat_implies_entails f6550 [c6227, c6490, c6541, c4772, c5549, c4352, c6371, c6540, c4920, c6449, c6285, c3610, c6451, c5326, c6494, c6456, c4423, c5728, c6542, c6547, c4880, c3989, c4877, c5248, c5686, c6549, c2699, c2729, c2736, c3133] c6550 unsat6550 (by rfl) a
  have h0 : Entails.eval a c6227 := derived6227 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6541 := derived6541 a h
  have h3 : Entails.eval a c4772 := h 4771 (by decide)
  have h4 : Entails.eval a c5549 := h 5548 (by decide)
  have h5 : Entails.eval a c4352 := h 4351 (by decide)
  have h6 : Entails.eval a c6371 := derived6371 a h
  have h7 : Entails.eval a c6540 := derived6540 a h
  have h8 : Entails.eval a c4920 := h 4919 (by decide)
  have h9 : Entails.eval a c6449 := derived6449 a h
  have h10 : Entails.eval a c6285 := derived6285 a h
  have h11 : Entails.eval a c3610 := h 3609 (by decide)
  have h12 : Entails.eval a c6451 := derived6451 a h
  have h13 : Entails.eval a c5326 := h 5325 (by decide)
  have h14 : Entails.eval a c6494 := derived6494 a h
  have h15 : Entails.eval a c6456 := derived6456 a h
  have h16 : Entails.eval a c4423 := h 4422 (by decide)
  have h17 : Entails.eval a c5728 := h 5727 (by decide)
  have h18 : Entails.eval a c6542 := derived6542 a h
  have h19 : Entails.eval a c6547 := derived6547 a h
  have h20 : Entails.eval a c4880 := h 4879 (by decide)
  have h21 : Entails.eval a c3989 := h 3988 (by decide)
  have h22 : Entails.eval a c4877 := h 4876 (by decide)
  have h23 : Entails.eval a c5248 := h 5247 (by decide)
  have h24 : Entails.eval a c5686 := h 5685 (by decide)
  have h25 : Entails.eval a c6549 := derived6549 a h
  have h26 : Entails.eval a c2699 := h 2698 (by decide)
  have h27 : Entails.eval a c2729 := h 2728 (by decide)
  have h28 : Entails.eval a c2736 := h 2735 (by decide)
  have h29 : Entails.eval a c3133 := h 3132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6551 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6541, some c6540, some c6371, some c6227, some c6480, some c3854, some c4235, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked6551 : lratChecker f6551 p6551 = .success := by decide +kernel
theorem unsat6551 : Unsatisfiable (PosFin 65) f6551 := by
  apply lratCheckerSound f6551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6551
  · intro a ha; simp [p6551] at ha; subst a; trivial
  · exact checked6551
theorem derived6551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6551 := by
  apply localUnsat_implies_entails f6551 [c6541, c6540, c6371, c6227, c6480, c3854, c4235] c6551 unsat6551 (by rfl) a
  have h0 : Entails.eval a c6541 := derived6541 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6480 := derived6480 a h
  have h5 : Entails.eval a c3854 := h 3853 (by decide)
  have h6 : Entails.eval a c4235 := h 4234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6552 : DefaultClause 65 := directClause [(⟨44, by decide⟩, false), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6541, some c6551, some c6452, some c6550, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked6552 : lratChecker f6552 p6552 = .success := by decide +kernel
theorem unsat6552 : Unsatisfiable (PosFin 65) f6552 := by
  apply lratCheckerSound f6552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6552
  · intro a ha; simp [p6552] at ha; subst a; trivial
  · exact checked6552
theorem derived6552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6552 := by
  apply localUnsat_implies_entails f6552 [c6540, c6541, c6551, c6452, c6550] c6552 unsat6552 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6541 := derived6541 a h
  have h2 : Entails.eval a c6551 := derived6551 a h
  have h3 : Entails.eval a c6452 := derived6452 a h
  have h4 : Entails.eval a c6550 := derived6550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c6553 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6552, some c6540, some c6490, some c6227, some c5558, some c4455, some c4778, some c4352, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6553 : lratChecker f6553 p6553 = .success := by decide +kernel
theorem unsat6553 : Unsatisfiable (PosFin 65) f6553 := by
  apply lratCheckerSound f6553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6553
  · intro a ha; simp [p6553] at ha; subst a; trivial
  · exact checked6553
theorem derived6553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6553 := by
  apply localUnsat_implies_entails f6553 [c6552, c6540, c6490, c6227, c5558, c4455, c4778, c4352] c6553 unsat6553 (by rfl) a
  have h0 : Entails.eval a c6552 := derived6552 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c5558 := h 5557 (by decide)
  have h5 : Entails.eval a c4455 := h 4454 (by decide)
  have h6 : Entails.eval a c4778 := h 4777 (by decide)
  have h7 : Entails.eval a c4352 := h 4351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6554 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6490, some c6371, some c6227, some c6552, some c6553, some c6302, some c4674, some c4397, some c5226, some c4352, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6554 : lratChecker f6554 p6554 = .success := by decide +kernel
theorem unsat6554 : Unsatisfiable (PosFin 65) f6554 := by
  apply lratCheckerSound f6554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6554
  · intro a ha; simp [p6554] at ha; subst a; trivial
  · exact checked6554
theorem derived6554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6554 := by
  apply localUnsat_implies_entails f6554 [c6540, c6490, c6371, c6227, c6552, c6553, c6302, c4674, c4397, c5226, c4352] c6554 unsat6554 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6552 := derived6552 a h
  have h5 : Entails.eval a c6553 := derived6553 a h
  have h6 : Entails.eval a c6302 := derived6302 a h
  have h7 : Entails.eval a c4674 := h 4673 (by decide)
  have h8 : Entails.eval a c4397 := h 4396 (by decide)
  have h9 : Entails.eval a c5226 := h 5225 (by decide)
  have h10 : Entails.eval a c4352 := h 4351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6555 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6490, some c6227, some c4344, some c4351, some c4343, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6555 : lratChecker f6555 p6555 = .success := by decide +kernel
theorem unsat6555 : Unsatisfiable (PosFin 65) f6555 := by
  apply lratCheckerSound f6555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6555
  · intro a ha; simp [p6555] at ha; subst a; trivial
  · exact checked6555
theorem derived6555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6555 := by
  apply localUnsat_implies_entails f6555 [c6554, c6490, c6227, c4344, c4351, c4343] c6555 unsat6555 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c4344 := h 4343 (by decide)
  have h4 : Entails.eval a c4351 := h 4350 (by decide)
  have h5 : Entails.eval a c4343 := h 4342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6556 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6555, some c6554, some c6540, some c6413, some c4121, some c6253, some c3961, some c6530, some c6460, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6556 : lratChecker f6556 p6556 = .success := by decide +kernel
theorem unsat6556 : Unsatisfiable (PosFin 65) f6556 := by
  apply lratCheckerSound f6556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6556
  · intro a ha; simp [p6556] at ha; subst a; trivial
  · exact checked6556
theorem derived6556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6556 := by
  apply localUnsat_implies_entails f6556 [c6555, c6554, c6540, c6413, c4121, c6253, c3961, c6530, c6460] c6556 unsat6556 (by rfl) a
  have h0 : Entails.eval a c6555 := derived6555 a h
  have h1 : Entails.eval a c6554 := derived6554 a h
  have h2 : Entails.eval a c6540 := derived6540 a h
  have h3 : Entails.eval a c6413 := derived6413 a h
  have h4 : Entails.eval a c4121 := h 4120 (by decide)
  have h5 : Entails.eval a c6253 := derived6253 a h
  have h6 : Entails.eval a c3961 := h 3960 (by decide)
  have h7 : Entails.eval a c6530 := derived6530 a h
  have h8 : Entails.eval a c6460 := derived6460 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6557 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6540, some c6490, some c6227, some c6555, some c6556, some c4879, some c4522, some c4434, some c4113, some c5470, some c6460, some c4158, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6557 : lratChecker f6557 p6557 = .success := by decide +kernel
theorem unsat6557 : Unsatisfiable (PosFin 65) f6557 := by
  apply lratCheckerSound f6557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6557
  · intro a ha; simp [p6557] at ha; subst a; trivial
  · exact checked6557
theorem derived6557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6557 := by
  apply localUnsat_implies_entails f6557 [c6554, c6540, c6490, c6227, c6555, c6556, c4879, c4522, c4434, c4113, c5470, c6460, c4158] c6557 unsat6557 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6555 := derived6555 a h
  have h5 : Entails.eval a c6556 := derived6556 a h
  have h6 : Entails.eval a c4879 := h 4878 (by decide)
  have h7 : Entails.eval a c4522 := h 4521 (by decide)
  have h8 : Entails.eval a c4434 := h 4433 (by decide)
  have h9 : Entails.eval a c4113 := h 4112 (by decide)
  have h10 : Entails.eval a c5470 := h 5469 (by decide)
  have h11 : Entails.eval a c6460 := derived6460 a h
  have h12 : Entails.eval a c4158 := h 4157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6558 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨36, by decide⟩, false), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6557, some c6540, some c6490, some c6227, some c5868, some c6505, some c6306, some c5488, some c4113, some c6369, some c4234, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked6558 : lratChecker f6558 p6558 = .success := by decide +kernel
theorem unsat6558 : Unsatisfiable (PosFin 65) f6558 := by
  apply lratCheckerSound f6558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6558
  · intro a ha; simp [p6558] at ha; subst a; trivial
  · exact checked6558
theorem derived6558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6558 := by
  apply localUnsat_implies_entails f6558 [c6557, c6540, c6490, c6227, c5868, c6505, c6306, c5488, c4113, c6369, c4234] c6558 unsat6558 (by rfl) a
  have h0 : Entails.eval a c6557 := derived6557 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c5868 := h 5867 (by decide)
  have h5 : Entails.eval a c6505 := derived6505 a h
  have h6 : Entails.eval a c6306 := derived6306 a h
  have h7 : Entails.eval a c5488 := h 5487 (by decide)
  have h8 : Entails.eval a c4113 := h 4112 (by decide)
  have h9 : Entails.eval a c6369 := derived6369 a h
  have h10 : Entails.eval a c4234 := h 4233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6559 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨36, by decide⟩, false), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6558, some c6557, some c6554, some c6540, some c6490, some c6371, some c6227, some c4524, some c4121, some c6253, some c6498, some c3961, some c6530, some c6402, some c5293, some c6241, some c6439, some c5067, some c5122, some c5015, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked6559 : lratChecker f6559 p6559 = .success := by decide +kernel
theorem unsat6559 : Unsatisfiable (PosFin 65) f6559 := by
  apply lratCheckerSound f6559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6559
  · intro a ha; simp [p6559] at ha; subst a; trivial
  · exact checked6559
theorem derived6559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6559 := by
  apply localUnsat_implies_entails f6559 [c6558, c6557, c6554, c6540, c6490, c6371, c6227, c4524, c4121, c6253, c6498, c3961, c6530, c6402, c5293, c6241, c6439, c5067, c5122, c5015] c6559 unsat6559 (by rfl) a
  have h0 : Entails.eval a c6558 := derived6558 a h
  have h1 : Entails.eval a c6557 := derived6557 a h
  have h2 : Entails.eval a c6554 := derived6554 a h
  have h3 : Entails.eval a c6540 := derived6540 a h
  have h4 : Entails.eval a c6490 := derived6490 a h
  have h5 : Entails.eval a c6371 := derived6371 a h
  have h6 : Entails.eval a c6227 := derived6227 a h
  have h7 : Entails.eval a c4524 := h 4523 (by decide)
  have h8 : Entails.eval a c4121 := h 4120 (by decide)
  have h9 : Entails.eval a c6253 := derived6253 a h
  have h10 : Entails.eval a c6498 := derived6498 a h
  have h11 : Entails.eval a c3961 := h 3960 (by decide)
  have h12 : Entails.eval a c6530 := derived6530 a h
  have h13 : Entails.eval a c6402 := derived6402 a h
  have h14 : Entails.eval a c5293 := h 5292 (by decide)
  have h15 : Entails.eval a c6241 := derived6241 a h
  have h16 : Entails.eval a c6439 := derived6439 a h
  have h17 : Entails.eval a c5067 := h 5066 (by decide)
  have h18 : Entails.eval a c5122 := h 5121 (by decide)
  have h19 : Entails.eval a c5015 := h 5014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6560 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6490, some c6227, some c6498, some c4485, some c4166, some c3751, some c6301, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked6560 : lratChecker f6560 p6560 = .success := by decide +kernel
theorem unsat6560 : Unsatisfiable (PosFin 65) f6560 := by
  apply lratCheckerSound f6560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6560
  · intro a ha; simp [p6560] at ha; subst a; trivial
  · exact checked6560
theorem derived6560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6560 := by
  apply localUnsat_implies_entails f6560 [c6554, c6490, c6227, c6498, c4485, c4166, c3751, c6301] c6560 unsat6560 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6490 := derived6490 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6498 := derived6498 a h
  have h4 : Entails.eval a c4485 := h 4484 (by decide)
  have h5 : Entails.eval a c4166 := h 4165 (by decide)
  have h6 : Entails.eval a c3751 := h 3750 (by decide)
  have h7 : Entails.eval a c6301 := derived6301 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6561 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6540, some c6490, some c6227, some c6557, some c6558, some c6559, some c3515, some c6560, some c4121, some c4143, some c6502, some c6439, some c5879, some c5044, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked6561 : lratChecker f6561 p6561 = .success := by decide +kernel
theorem unsat6561 : Unsatisfiable (PosFin 65) f6561 := by
  apply lratCheckerSound f6561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6561
  · intro a ha; simp [p6561] at ha; subst a; trivial
  · exact checked6561
theorem derived6561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6561 := by
  apply localUnsat_implies_entails f6561 [c6554, c6540, c6490, c6227, c6557, c6558, c6559, c3515, c6560, c4121, c4143, c6502, c6439, c5879, c5044] c6561 unsat6561 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6557 := derived6557 a h
  have h5 : Entails.eval a c6558 := derived6558 a h
  have h6 : Entails.eval a c6559 := derived6559 a h
  have h7 : Entails.eval a c3515 := h 3514 (by decide)
  have h8 : Entails.eval a c6560 := derived6560 a h
  have h9 : Entails.eval a c4121 := h 4120 (by decide)
  have h10 : Entails.eval a c4143 := h 4142 (by decide)
  have h11 : Entails.eval a c6502 := derived6502 a h
  have h12 : Entails.eval a c6439 := derived6439 a h
  have h13 : Entails.eval a c5879 := h 5878 (by decide)
  have h14 : Entails.eval a c5044 := h 5043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6562 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6561, some c6554, some c6540, some c6490, some c6371, some c6227, some c4844, some c4121, some c6253, some c6498, some c4828, some c6402, some c5918, some c3961, some c5293, some c6241, some c6439, some c5067, some c5122, some c5015, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked6562 : lratChecker f6562 p6562 = .success := by decide +kernel
theorem unsat6562 : Unsatisfiable (PosFin 65) f6562 := by
  apply lratCheckerSound f6562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6562
  · intro a ha; simp [p6562] at ha; subst a; trivial
  · exact checked6562
theorem derived6562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6562 := by
  apply localUnsat_implies_entails f6562 [c6561, c6554, c6540, c6490, c6371, c6227, c4844, c4121, c6253, c6498, c4828, c6402, c5918, c3961, c5293, c6241, c6439, c5067, c5122, c5015] c6562 unsat6562 (by rfl) a
  have h0 : Entails.eval a c6561 := derived6561 a h
  have h1 : Entails.eval a c6554 := derived6554 a h
  have h2 : Entails.eval a c6540 := derived6540 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6371 := derived6371 a h
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c4844 := h 4843 (by decide)
  have h7 : Entails.eval a c4121 := h 4120 (by decide)
  have h8 : Entails.eval a c6253 := derived6253 a h
  have h9 : Entails.eval a c6498 := derived6498 a h
  have h10 : Entails.eval a c4828 := h 4827 (by decide)
  have h11 : Entails.eval a c6402 := derived6402 a h
  have h12 : Entails.eval a c5918 := derived5918 a h
  have h13 : Entails.eval a c3961 := h 3960 (by decide)
  have h14 : Entails.eval a c5293 := h 5292 (by decide)
  have h15 : Entails.eval a c6241 := derived6241 a h
  have h16 : Entails.eval a c6439 := derived6439 a h
  have h17 : Entails.eval a c5067 := h 5066 (by decide)
  have h18 : Entails.eval a c5122 := h 5121 (by decide)
  have h19 : Entails.eval a c5015 := h 5014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6563 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6540, some c6490, some c6371, some c6227, some c6562, some c5868, some c6505, some c5488, some c4113, some c4234, some c4158, some c6369, some c6518, some c4612, some c6433, some c6241, some c6439, some c5067, some c5122, some c5015, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked6563 : lratChecker f6563 p6563 = .success := by decide +kernel
theorem unsat6563 : Unsatisfiable (PosFin 65) f6563 := by
  apply lratCheckerSound f6563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6563
  · intro a ha; simp [p6563] at ha; subst a; trivial
  · exact checked6563
theorem derived6563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6563 := by
  apply localUnsat_implies_entails f6563 [c6554, c6540, c6490, c6371, c6227, c6562, c5868, c6505, c5488, c4113, c4234, c4158, c6369, c6518, c4612, c6433, c6241, c6439, c5067, c5122, c5015] c6563 unsat6563 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6371 := derived6371 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6562 := derived6562 a h
  have h6 : Entails.eval a c5868 := h 5867 (by decide)
  have h7 : Entails.eval a c6505 := derived6505 a h
  have h8 : Entails.eval a c5488 := h 5487 (by decide)
  have h9 : Entails.eval a c4113 := h 4112 (by decide)
  have h10 : Entails.eval a c4234 := h 4233 (by decide)
  have h11 : Entails.eval a c4158 := h 4157 (by decide)
  have h12 : Entails.eval a c6369 := derived6369 a h
  have h13 : Entails.eval a c6518 := derived6518 a h
  have h14 : Entails.eval a c4612 := h 4611 (by decide)
  have h15 : Entails.eval a c6433 := derived6433 a h
  have h16 : Entails.eval a c6241 := derived6241 a h
  have h17 : Entails.eval a c6439 := derived6439 a h
  have h18 : Entails.eval a c5067 := h 5066 (by decide)
  have h19 : Entails.eval a c5122 := h 5121 (by decide)
  have h20 : Entails.eval a c5015 := h 5014 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6564 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6563, some c6561, some c6554, some c6540, some c6490, some c6227, some c4843, some c4113, some c5470, some c4234, some c4158, some c6518, some c6460, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6564 : lratChecker f6564 p6564 = .success := by decide +kernel
theorem unsat6564 : Unsatisfiable (PosFin 65) f6564 := by
  apply lratCheckerSound f6564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6564
  · intro a ha; simp [p6564] at ha; subst a; trivial
  · exact checked6564
theorem derived6564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6564 := by
  apply localUnsat_implies_entails f6564 [c6563, c6561, c6554, c6540, c6490, c6227, c4843, c4113, c5470, c4234, c4158, c6518, c6460] c6564 unsat6564 (by rfl) a
  have h0 : Entails.eval a c6563 := derived6563 a h
  have h1 : Entails.eval a c6561 := derived6561 a h
  have h2 : Entails.eval a c6554 := derived6554 a h
  have h3 : Entails.eval a c6540 := derived6540 a h
  have h4 : Entails.eval a c6490 := derived6490 a h
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c4843 := h 4842 (by decide)
  have h7 : Entails.eval a c4113 := h 4112 (by decide)
  have h8 : Entails.eval a c5470 := h 5469 (by decide)
  have h9 : Entails.eval a c4234 := h 4233 (by decide)
  have h10 : Entails.eval a c4158 := h 4157 (by decide)
  have h11 : Entails.eval a c6518 := derived6518 a h
  have h12 : Entails.eval a c6460 := derived6460 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6565 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6540, some c6561, some c6563, some c6564, some c4844, some c4121, some c6253, some c4828, some c6460, some c5918, some c3961, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6565 : lratChecker f6565 p6565 = .success := by decide +kernel
theorem unsat6565 : Unsatisfiable (PosFin 65) f6565 := by
  apply lratCheckerSound f6565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6565
  · intro a ha; simp [p6565] at ha; subst a; trivial
  · exact checked6565
theorem derived6565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6565 := by
  apply localUnsat_implies_entails f6565 [c6554, c6540, c6561, c6563, c6564, c4844, c4121, c6253, c4828, c6460, c5918, c3961] c6565 unsat6565 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6561 := derived6561 a h
  have h3 : Entails.eval a c6563 := derived6563 a h
  have h4 : Entails.eval a c6564 := derived6564 a h
  have h5 : Entails.eval a c4844 := h 4843 (by decide)
  have h6 : Entails.eval a c4121 := h 4120 (by decide)
  have h7 : Entails.eval a c6253 := derived6253 a h
  have h8 : Entails.eval a c4828 := h 4827 (by decide)
  have h9 : Entails.eval a c6460 := derived6460 a h
  have h10 : Entails.eval a c5918 := derived5918 a h
  have h11 : Entails.eval a c3961 := h 3960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6566 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨53, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6565, some c6554, some c6537, some c4244, some c6496, some c5273, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6566 : lratChecker f6566 p6566 = .success := by decide +kernel
theorem unsat6566 : Unsatisfiable (PosFin 65) f6566 := by
  apply lratCheckerSound f6566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6566
  · intro a ha; simp [p6566] at ha; subst a; trivial
  · exact checked6566
theorem derived6566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6566 := by
  apply localUnsat_implies_entails f6566 [c6565, c6554, c6537, c4244, c6496, c5273] c6566 unsat6566 (by rfl) a
  have h0 : Entails.eval a c6565 := derived6565 a h
  have h1 : Entails.eval a c6554 := derived6554 a h
  have h2 : Entails.eval a c6537 := derived6537 a h
  have h3 : Entails.eval a c4244 := h 4243 (by decide)
  have h4 : Entails.eval a c6496 := derived6496 a h
  have h5 : Entails.eval a c5273 := h 5272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6567 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6565, some c6554, some c6371, some c6537, some c6466, some c6566, some c4121, some c4547, some c5615, some c4506, some c4502, some c4500, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked6567 : lratChecker f6567 p6567 = .success := by decide +kernel
theorem unsat6567 : Unsatisfiable (PosFin 65) f6567 := by
  apply lratCheckerSound f6567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6567
  · intro a ha; simp [p6567] at ha; subst a; trivial
  · exact checked6567
theorem derived6567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6567 := by
  apply localUnsat_implies_entails f6567 [c6565, c6554, c6371, c6537, c6466, c6566, c4121, c4547, c5615, c4506, c4502, c4500] c6567 unsat6567 (by rfl) a
  have h0 : Entails.eval a c6565 := derived6565 a h
  have h1 : Entails.eval a c6554 := derived6554 a h
  have h2 : Entails.eval a c6371 := derived6371 a h
  have h3 : Entails.eval a c6537 := derived6537 a h
  have h4 : Entails.eval a c6466 := derived6466 a h
  have h5 : Entails.eval a c6566 := derived6566 a h
  have h6 : Entails.eval a c4121 := h 4120 (by decide)
  have h7 : Entails.eval a c4547 := h 4546 (by decide)
  have h8 : Entails.eval a c5615 := h 5614 (by decide)
  have h9 : Entails.eval a c4506 := h 4505 (by decide)
  have h10 : Entails.eval a c4502 := h 4501 (by decide)
  have h11 : Entails.eval a c4500 := h 4499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6568 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6567, some c6565, some c6554, some c6540, some c6490, some c6227, some c3491, some c4284, some c6434, some c3639, some c5488, some c6460, some c5782, some c6435, some c3892, some c5661, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked6568 : lratChecker f6568 p6568 = .success := by decide +kernel
theorem unsat6568 : Unsatisfiable (PosFin 65) f6568 := by
  apply lratCheckerSound f6568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6568
  · intro a ha; simp [p6568] at ha; subst a; trivial
  · exact checked6568
theorem derived6568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6568 := by
  apply localUnsat_implies_entails f6568 [c6567, c6565, c6554, c6540, c6490, c6227, c3491, c4284, c6434, c3639, c5488, c6460, c5782, c6435, c3892, c5661] c6568 unsat6568 (by rfl) a
  have h0 : Entails.eval a c6567 := derived6567 a h
  have h1 : Entails.eval a c6565 := derived6565 a h
  have h2 : Entails.eval a c6554 := derived6554 a h
  have h3 : Entails.eval a c6540 := derived6540 a h
  have h4 : Entails.eval a c6490 := derived6490 a h
  have h5 : Entails.eval a c6227 := derived6227 a h
  have h6 : Entails.eval a c3491 := h 3490 (by decide)
  have h7 : Entails.eval a c4284 := h 4283 (by decide)
  have h8 : Entails.eval a c6434 := derived6434 a h
  have h9 : Entails.eval a c3639 := h 3638 (by decide)
  have h10 : Entails.eval a c5488 := h 5487 (by decide)
  have h11 : Entails.eval a c6460 := derived6460 a h
  have h12 : Entails.eval a c5782 := h 5781 (by decide)
  have h13 : Entails.eval a c6435 := derived6435 a h
  have h14 : Entails.eval a c3892 := h 3891 (by decide)
  have h15 : Entails.eval a c5661 := h 5660 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6569 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨34, by decide⟩, true), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6227, some c6518, some c5675, some c5364, some c4158, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6569 : lratChecker f6569 p6569 = .success := by decide +kernel
theorem unsat6569 : Unsatisfiable (PosFin 65) f6569 := by
  apply lratCheckerSound f6569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6569
  · intro a ha; simp [p6569] at ha; subst a; trivial
  · exact checked6569
theorem derived6569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6569 := by
  apply localUnsat_implies_entails f6569 [c6540, c6227, c6518, c5675, c5364, c4158] c6569 unsat6569 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6227 := derived6227 a h
  have h2 : Entails.eval a c6518 := derived6518 a h
  have h3 : Entails.eval a c5675 := h 5674 (by decide)
  have h4 : Entails.eval a c5364 := h 5363 (by decide)
  have h5 : Entails.eval a c4158 := h 4157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6570 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6565, some c6540, some c6227, some c6567, some c6568, some c6569, some c6496, some c4234, some c5364, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked6570 : lratChecker f6570 p6570 = .success := by decide +kernel
theorem unsat6570 : Unsatisfiable (PosFin 65) f6570 := by
  apply lratCheckerSound f6570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6570
  · intro a ha; simp [p6570] at ha; subst a; trivial
  · exact checked6570
theorem derived6570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6570 := by
  apply localUnsat_implies_entails f6570 [c6565, c6540, c6227, c6567, c6568, c6569, c6496, c4234, c5364] c6570 unsat6570 (by rfl) a
  have h0 : Entails.eval a c6565 := derived6565 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6227 := derived6227 a h
  have h3 : Entails.eval a c6567 := derived6567 a h
  have h4 : Entails.eval a c6568 := derived6568 a h
  have h5 : Entails.eval a c6569 := derived6569 a h
  have h6 : Entails.eval a c6496 := derived6496 a h
  have h7 : Entails.eval a c4234 := h 4233 (by decide)
  have h8 : Entails.eval a c5364 := h 5363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6571 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6570, some c6565, some c6490, some c6227, some c6498, some c6569, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6571 : lratChecker f6571 p6571 = .success := by decide +kernel
theorem unsat6571 : Unsatisfiable (PosFin 65) f6571 := by
  apply lratCheckerSound f6571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6571
  · intro a ha; simp [p6571] at ha; subst a; trivial
  · exact checked6571
theorem derived6571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6571 := by
  apply localUnsat_implies_entails f6571 [c6570, c6565, c6490, c6227, c6498, c6569] c6571 unsat6571 (by rfl) a
  have h0 : Entails.eval a c6570 := derived6570 a h
  have h1 : Entails.eval a c6565 := derived6565 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6498 := derived6498 a h
  have h5 : Entails.eval a c6569 := derived6569 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6572 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6570, some c6565, some c6540, some c6490, some c6227, some c6571, some c4113, some c3491, some c6434, some c6306, some c5488, some c6520, some c4860, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked6572 : lratChecker f6572 p6572 = .success := by decide +kernel
theorem unsat6572 : Unsatisfiable (PosFin 65) f6572 := by
  apply lratCheckerSound f6572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6572
  · intro a ha; simp [p6572] at ha; subst a; trivial
  · exact checked6572
theorem derived6572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6572 := by
  apply localUnsat_implies_entails f6572 [c6570, c6565, c6540, c6490, c6227, c6571, c4113, c3491, c6434, c6306, c5488, c6520, c4860] c6572 unsat6572 (by rfl) a
  have h0 : Entails.eval a c6570 := derived6570 a h
  have h1 : Entails.eval a c6565 := derived6565 a h
  have h2 : Entails.eval a c6540 := derived6540 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6227 := derived6227 a h
  have h5 : Entails.eval a c6571 := derived6571 a h
  have h6 : Entails.eval a c4113 := h 4112 (by decide)
  have h7 : Entails.eval a c3491 := h 3490 (by decide)
  have h8 : Entails.eval a c6434 := derived6434 a h
  have h9 : Entails.eval a c6306 := derived6306 a h
  have h10 : Entails.eval a c5488 := h 5487 (by decide)
  have h11 : Entails.eval a c6520 := derived6520 a h
  have h12 : Entails.eval a c4860 := h 4859 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6573 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6554, some c6540, some c6490, some c6227, some c6565, some c6572, some c6537, some c6566, some c6466, some c4121, some c3492, some c4547, some c5615, some c5309, some c6467, some c4720, some c4367, some c4375, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6573 : lratChecker f6573 p6573 = .success := by decide +kernel
theorem unsat6573 : Unsatisfiable (PosFin 65) f6573 := by
  apply lratCheckerSound f6573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6573
  · intro a ha; simp [p6573] at ha; subst a; trivial
  · exact checked6573
theorem derived6573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6573 := by
  apply localUnsat_implies_entails f6573 [c6554, c6540, c6490, c6227, c6565, c6572, c6537, c6566, c6466, c4121, c3492, c4547, c5615, c5309, c6467, c4720, c4367, c4375] c6573 unsat6573 (by rfl) a
  have h0 : Entails.eval a c6554 := derived6554 a h
  have h1 : Entails.eval a c6540 := derived6540 a h
  have h2 : Entails.eval a c6490 := derived6490 a h
  have h3 : Entails.eval a c6227 := derived6227 a h
  have h4 : Entails.eval a c6565 := derived6565 a h
  have h5 : Entails.eval a c6572 := derived6572 a h
  have h6 : Entails.eval a c6537 := derived6537 a h
  have h7 : Entails.eval a c6566 := derived6566 a h
  have h8 : Entails.eval a c6466 := derived6466 a h
  have h9 : Entails.eval a c4121 := h 4120 (by decide)
  have h10 : Entails.eval a c3492 := h 3491 (by decide)
  have h11 : Entails.eval a c4547 := h 4546 (by decide)
  have h12 : Entails.eval a c5615 := h 5614 (by decide)
  have h13 : Entails.eval a c5309 := h 5308 (by decide)
  have h14 : Entails.eval a c6467 := derived6467 a h
  have h15 : Entails.eval a c4720 := h 4719 (by decide)
  have h16 : Entails.eval a c4367 := h 4366 (by decide)
  have h17 : Entails.eval a c4375 := h 4374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6574 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6540, some c6573, some c6554, some c6538, some c6537, some c5544, some c6458, some c4925, some c6555, some c4547, some c6491, some c5664, some c6460, some c4244, some c6490, some c6227, some c4227, some c4437, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked6574 : lratChecker f6574 p6574 = .success := by decide +kernel
theorem unsat6574 : Unsatisfiable (PosFin 65) f6574 := by
  apply lratCheckerSound f6574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6574
  · intro a ha; simp [p6574] at ha; subst a; trivial
  · exact checked6574
theorem derived6574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6574 := by
  apply localUnsat_implies_entails f6574 [c6540, c6573, c6554, c6538, c6537, c5544, c6458, c4925, c6555, c4547, c6491, c5664, c6460, c4244, c6490, c6227, c4227, c4437] c6574 unsat6574 (by rfl) a
  have h0 : Entails.eval a c6540 := derived6540 a h
  have h1 : Entails.eval a c6573 := derived6573 a h
  have h2 : Entails.eval a c6554 := derived6554 a h
  have h3 : Entails.eval a c6538 := derived6538 a h
  have h4 : Entails.eval a c6537 := derived6537 a h
  have h5 : Entails.eval a c5544 := h 5543 (by decide)
  have h6 : Entails.eval a c6458 := derived6458 a h
  have h7 : Entails.eval a c4925 := h 4924 (by decide)
  have h8 : Entails.eval a c6555 := derived6555 a h
  have h9 : Entails.eval a c4547 := h 4546 (by decide)
  have h10 : Entails.eval a c6491 := derived6491 a h
  have h11 : Entails.eval a c5664 := h 5663 (by decide)
  have h12 : Entails.eval a c6460 := derived6460 a h
  have h13 : Entails.eval a c4244 := h 4243 (by decide)
  have h14 : Entails.eval a c6490 := derived6490 a h
  have h15 : Entails.eval a c6227 := derived6227 a h
  have h16 : Entails.eval a c4227 := h 4226 (by decide)
  have h17 : Entails.eval a c4437 := h 4436 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6575 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨50, by decide⟩, false), (⟨60, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨57, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2701, some c2731, some c2739, some c3131, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p6575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6575 : lratChecker f6575 p6575 = .success := by decide +kernel
theorem unsat6575 : Unsatisfiable (PosFin 65) f6575 := by
  apply lratCheckerSound f6575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6575
  · intro a ha; simp [p6575] at ha; subst a; trivial
  · exact checked6575
theorem derived6575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6575 := by
  apply localUnsat_implies_entails f6575 [c2701, c2731, c2739, c3131] c6575 unsat6575 (by rfl) a
  have h0 : Entails.eval a c2701 := h 2700 (by decide)
  have h1 : Entails.eval a c2731 := h 2730 (by decide)
  have h2 : Entails.eval a c2739 := h 2738 (by decide)
  have h3 : Entails.eval a c3131 := h 3130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6576 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨45, by decide⟩, true), (⟨52, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨46, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3132, some c3087, some c2786, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p6576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked6576 : lratChecker f6576 p6576 = .success := by decide +kernel
theorem unsat6576 : Unsatisfiable (PosFin 65) f6576 := by
  apply lratCheckerSound f6576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6576
  · intro a ha; simp [p6576] at ha; subst a; trivial
  · exact checked6576
theorem derived6576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6576 := by
  apply localUnsat_implies_entails f6576 [c3132, c3087, c2786] c6576 unsat6576 (by rfl) a
  have h0 : Entails.eval a c3132 := h 3131 (by decide)
  have h1 : Entails.eval a c3087 := h 3086 (by decide)
  have h2 : Entails.eval a c2786 := h 2785 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c6577 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨45, by decide⟩, true), (⟨62, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨57, by decide⟩, false), (⟨46, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6576, some c2747, some c3035, some c3048, some c3057, some c3182, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p6577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked6577 : lratChecker f6577 p6577 = .success := by decide +kernel
theorem unsat6577 : Unsatisfiable (PosFin 65) f6577 := by
  apply lratCheckerSound f6577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6577
  · intro a ha; simp [p6577] at ha; subst a; trivial
  · exact checked6577
theorem derived6577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6577 := by
  apply localUnsat_implies_entails f6577 [c6576, c2747, c3035, c3048, c3057, c3182] c6577 unsat6577 (by rfl) a
  have h0 : Entails.eval a c6576 := derived6576 a h
  have h1 : Entails.eval a c2747 := h 2746 (by decide)
  have h2 : Entails.eval a c3035 := h 3034 (by decide)
  have h3 : Entails.eval a c3048 := h 3047 (by decide)
  have h4 : Entails.eval a c3057 := h 3056 (by decide)
  have h5 : Entails.eval a c3182 := h 3181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6578 : DefaultClause 65 := directClause [(⟨45, by decide⟩, true), (⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6574, some c6573, some c6554, some c6538, some c6537, some c5544, some c6540, some c6458, some c6555, some c4925, some c4547, some c6491, some c4244, some c3492, some c6371, some c6473, some c6542, some c5664, some c6460, some c6173, some c6439, some c5938, some c3670, some c6490, some c3640, some c4428, some c6575, some c6577, some c2852, some c2854, some c3246, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked6578 : lratChecker f6578 p6578 = .success := by decide +kernel
theorem unsat6578 : Unsatisfiable (PosFin 65) f6578 := by
  apply lratCheckerSound f6578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6578
  · intro a ha; simp [p6578] at ha; subst a; trivial
  · exact checked6578
theorem derived6578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6578 := by
  apply localUnsat_implies_entails f6578 [c6574, c6573, c6554, c6538, c6537, c5544, c6540, c6458, c6555, c4925, c4547, c6491, c4244, c3492, c6371, c6473, c6542, c5664, c6460, c6173, c6439, c5938, c3670, c6490, c3640, c4428, c6575, c6577, c2852, c2854, c3246] c6578 unsat6578 (by rfl) a
  have h0 : Entails.eval a c6574 := derived6574 a h
  have h1 : Entails.eval a c6573 := derived6573 a h
  have h2 : Entails.eval a c6554 := derived6554 a h
  have h3 : Entails.eval a c6538 := derived6538 a h
  have h4 : Entails.eval a c6537 := derived6537 a h
  have h5 : Entails.eval a c5544 := h 5543 (by decide)
  have h6 : Entails.eval a c6540 := derived6540 a h
  have h7 : Entails.eval a c6458 := derived6458 a h
  have h8 : Entails.eval a c6555 := derived6555 a h
  have h9 : Entails.eval a c4925 := h 4924 (by decide)
  have h10 : Entails.eval a c4547 := h 4546 (by decide)
  have h11 : Entails.eval a c6491 := derived6491 a h
  have h12 : Entails.eval a c4244 := h 4243 (by decide)
  have h13 : Entails.eval a c3492 := h 3491 (by decide)
  have h14 : Entails.eval a c6371 := derived6371 a h
  have h15 : Entails.eval a c6473 := derived6473 a h
  have h16 : Entails.eval a c6542 := derived6542 a h
  have h17 : Entails.eval a c5664 := h 5663 (by decide)
  have h18 : Entails.eval a c6460 := derived6460 a h
  have h19 : Entails.eval a c6173 := derived6173 a h
  have h20 : Entails.eval a c6439 := derived6439 a h
  have h21 : Entails.eval a c5938 := derived5938 a h
  have h22 : Entails.eval a c3670 := h 3669 (by decide)
  have h23 : Entails.eval a c6490 := derived6490 a h
  have h24 : Entails.eval a c3640 := h 3639 (by decide)
  have h25 : Entails.eval a c4428 := h 4427 (by decide)
  have h26 : Entails.eval a c6575 := derived6575 a h
  have h27 : Entails.eval a c6577 := derived6577 a h
  have h28 : Entails.eval a c2852 := h 2851 (by decide)
  have h29 : Entails.eval a c2854 := h 2853 (by decide)
  have h30 : Entails.eval a c3246 := h 3245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c6579 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, false), (⟨45, by decide⟩, false), (⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, false), (⟨57, by decide⟩, false), (⟨36, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3226, some c3247, some c3198, some c3284, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p6579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked6579 : lratChecker f6579 p6579 = .success := by decide +kernel
theorem unsat6579 : Unsatisfiable (PosFin 65) f6579 := by
  apply lratCheckerSound f6579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6579
  · intro a ha; simp [p6579] at ha; subst a; trivial
  · exact checked6579
theorem derived6579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6579 := by
  apply localUnsat_implies_entails f6579 [c3226, c3247, c3198, c3284] c6579 unsat6579 (by rfl) a
  have h0 : Entails.eval a c3226 := h 3225 (by decide)
  have h1 : Entails.eval a c3247 := h 3246 (by decide)
  have h2 : Entails.eval a c3198 := h 3197 (by decide)
  have h3 : Entails.eval a c3284 := h 3283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c6580 : DefaultClause 65 := directClause [(⟨53, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6573, some c6554, some c6540, some c6490, some c6371, some c6538, some c6537, some c6458, some c5544, some c6473, some c6555, some c4925, some c4547, some c6491, some c4244, some c6542, some c5664, some c3492, some c6460, some c3670, some c6439, some c5938, some c6574, some c6578, some c4880, some c4877, some c6575, some c6579, some c2778, some c3229, some c3237, some c3210, some c3352, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p6580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked6580 : lratChecker f6580 p6580 = .success := by decide +kernel
theorem unsat6580 : Unsatisfiable (PosFin 65) f6580 := by
  apply lratCheckerSound f6580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6580
  · intro a ha; simp [p6580] at ha; subst a; trivial
  · exact checked6580
theorem derived6580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6580 := by
  apply localUnsat_implies_entails f6580 [c6573, c6554, c6540, c6490, c6371, c6538, c6537, c6458, c5544, c6473, c6555, c4925, c4547, c6491, c4244, c6542, c5664, c3492, c6460, c3670, c6439, c5938, c6574, c6578, c4880, c4877, c6575, c6579, c2778, c3229, c3237, c3210, c3352] c6580 unsat6580 (by rfl) a
  have h0 : Entails.eval a c6573 := derived6573 a h
  have h1 : Entails.eval a c6554 := derived6554 a h
  have h2 : Entails.eval a c6540 := derived6540 a h
  have h3 : Entails.eval a c6490 := derived6490 a h
  have h4 : Entails.eval a c6371 := derived6371 a h
  have h5 : Entails.eval a c6538 := derived6538 a h
  have h6 : Entails.eval a c6537 := derived6537 a h
  have h7 : Entails.eval a c6458 := derived6458 a h
  have h8 : Entails.eval a c5544 := h 5543 (by decide)
  have h9 : Entails.eval a c6473 := derived6473 a h
  have h10 : Entails.eval a c6555 := derived6555 a h
  have h11 : Entails.eval a c4925 := h 4924 (by decide)
  have h12 : Entails.eval a c4547 := h 4546 (by decide)
  have h13 : Entails.eval a c6491 := derived6491 a h
  have h14 : Entails.eval a c4244 := h 4243 (by decide)
  have h15 : Entails.eval a c6542 := derived6542 a h
  have h16 : Entails.eval a c5664 := h 5663 (by decide)
  have h17 : Entails.eval a c3492 := h 3491 (by decide)
  have h18 : Entails.eval a c6460 := derived6460 a h
  have h19 : Entails.eval a c3670 := h 3669 (by decide)
  have h20 : Entails.eval a c6439 := derived6439 a h
  have h21 : Entails.eval a c5938 := derived5938 a h
  have h22 : Entails.eval a c6574 := derived6574 a h
  have h23 : Entails.eval a c6578 := derived6578 a h
  have h24 : Entails.eval a c4880 := h 4879 (by decide)
  have h25 : Entails.eval a c4877 := h 4876 (by decide)
  have h26 : Entails.eval a c6575 := derived6575 a h
  have h27 : Entails.eval a c6579 := derived6579 a h
  have h28 : Entails.eval a c2778 := h 2777 (by decide)
  have h29 : Entails.eval a c3229 := h 3228 (by decide)
  have h30 : Entails.eval a c3237 := h 3236 (by decide)
  have h31 : Entails.eval a c3210 := h 3209 (by decide)
  have h32 : Entails.eval a c3352 := h 3351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived6580

end CochromaticTwenty.Certificates.FixedCore1
