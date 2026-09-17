import MerLeanExperiment.Certificates.FixedCore1.Steps3400_3499

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9381 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9381 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9367, some c5436, some c4011, some c4689, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p9381 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9381 : lratChecker f9381 p9381 = .success := by decide +kernel
theorem unsat9381 : Unsatisfiable (PosFin 65) f9381 := by
  apply lratCheckerSound f9381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9381
  · intro a ha; simp [p9381] at ha; subst a; trivial
  · exact checked9381
theorem derived9381 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9381 := by
  apply localUnsat_implies_entails f9381 [c9229, c9367, c5436, c4011, c4689] c9381 unsat9381 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c5436 := h 5435 (by decide)
  have h3 : Entails.eval a c4011 := h 4010 (by decide)
  have h4 : Entails.eval a c4689 := h 4688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9382 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9382 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c3539, some c3555, some c3540, some c6112, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9382 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9382 : lratChecker f9382 p9382 = .success := by decide +kernel
theorem unsat9382 : Unsatisfiable (PosFin 65) f9382 := by
  apply lratCheckerSound f9382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9382
  · intro a ha; simp [p9382] at ha; subst a; trivial
  · exact checked9382
theorem derived9382 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9382 := by
  apply localUnsat_implies_entails f9382 [c9228, c3539, c3555, c3540, c6112] c9382 unsat9382 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c3539 := h 3538 (by decide)
  have h2 : Entails.eval a c3555 := h 3554 (by decide)
  have h3 : Entails.eval a c3540 := h 3539 (by decide)
  have h4 : Entails.eval a c6112 := derived6112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9383 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9383 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9367, some c9373, some c9376, some c9380, some c9381, some c3632, some c3524, some c9122, some c4689, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9383 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9383 : lratChecker f9383 p9383 = .success := by decide +kernel
theorem unsat9383 : Unsatisfiable (PosFin 65) f9383 := by
  apply lratCheckerSound f9383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9383
  · intro a ha; simp [p9383] at ha; subst a; trivial
  · exact checked9383
theorem derived9383 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9383 := by
  apply localUnsat_implies_entails f9383 [c9229, c9367, c9373, c9376, c9380, c9381, c3632, c3524, c9122, c4689] c9383 unsat9383 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9373 := derived9373 a h
  have h3 : Entails.eval a c9376 := derived9376 a h
  have h4 : Entails.eval a c9380 := derived9380 a h
  have h5 : Entails.eval a c9381 := derived9381 a h
  have h6 : Entails.eval a c3632 := h 3631 (by decide)
  have h7 : Entails.eval a c3524 := h 3523 (by decide)
  have h8 : Entails.eval a c9122 := derived9122 a h
  have h9 : Entails.eval a c4689 := h 4688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9384 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9384 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c6797, some c6984, some c6877, some c6786, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9384 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9384 : lratChecker f9384 p9384 = .success := by decide +kernel
theorem unsat9384 : Unsatisfiable (PosFin 65) f9384 := by
  apply lratCheckerSound f9384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9384
  · intro a ha; simp [p9384] at ha; subst a; trivial
  · exact checked9384
theorem derived9384 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9384 := by
  apply localUnsat_implies_entails f9384 [c9367, c6797, c6984, c6877, c6786] c9384 unsat9384 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c6797 := derived6797 a h
  have h2 : Entails.eval a c6984 := derived6984 a h
  have h3 : Entails.eval a c6877 := derived6877 a h
  have h4 : Entails.eval a c6786 := derived6786 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9385 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, true), (⟨57, by decide⟩, true), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9385 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9367, some c9122, some c4682, some c6873, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p9385 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9385 : lratChecker f9385 p9385 = .success := by decide +kernel
theorem unsat9385 : Unsatisfiable (PosFin 65) f9385 := by
  apply lratCheckerSound f9385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9385
  · intro a ha; simp [p9385] at ha; subst a; trivial
  · exact checked9385
theorem derived9385 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9385 := by
  apply localUnsat_implies_entails f9385 [c9229, c9367, c9122, c4682, c6873] c9385 unsat9385 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9122 := derived9122 a h
  have h3 : Entails.eval a c4682 := h 4681 (by decide)
  have h4 : Entails.eval a c6873 := derived6873 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9386 : DefaultClause 65 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9386 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9228, some c6873, some c4841, some c6883, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p9386 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9386 : lratChecker f9386 p9386 = .success := by decide +kernel
theorem unsat9386 : Unsatisfiable (PosFin 65) f9386 := by
  apply lratCheckerSound f9386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9386
  · intro a ha; simp [p9386] at ha; subst a; trivial
  · exact checked9386
theorem derived9386 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9386 := by
  apply localUnsat_implies_entails f9386 [c9367, c9228, c6873, c4841, c6883] c9386 unsat9386 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9228 := derived9228 a h
  have h2 : Entails.eval a c6873 := derived6873 a h
  have h3 : Entails.eval a c4841 := h 4840 (by decide)
  have h4 : Entails.eval a c6883 := derived6883 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9387 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9387 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c9367, some c9373, some c9383, some c9384, some c6830, some c6997, some c7008, some c6913, some c6806, some c6930, some c6786, some c9385, some c6810, some c9386, some c7046, some c5823, some c4314, some c6866, some c3857, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9387 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9387 : lratChecker f9387 p9387 = .success := by decide +kernel
theorem unsat9387 : Unsatisfiable (PosFin 65) f9387 := by
  apply lratCheckerSound f9387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9387
  · intro a ha; simp [p9387] at ha; subst a; trivial
  · exact checked9387
theorem derived9387 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9387 := by
  apply localUnsat_implies_entails f9387 [c9228, c9367, c9373, c9383, c9384, c6830, c6997, c7008, c6913, c6806, c6930, c6786, c9385, c6810, c9386, c7046, c5823, c4314, c6866, c3857] c9387 unsat9387 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9373 := derived9373 a h
  have h3 : Entails.eval a c9383 := derived9383 a h
  have h4 : Entails.eval a c9384 := derived9384 a h
  have h5 : Entails.eval a c6830 := derived6830 a h
  have h6 : Entails.eval a c6997 := derived6997 a h
  have h7 : Entails.eval a c7008 := derived7008 a h
  have h8 : Entails.eval a c6913 := derived6913 a h
  have h9 : Entails.eval a c6806 := derived6806 a h
  have h10 : Entails.eval a c6930 := derived6930 a h
  have h11 : Entails.eval a c6786 := derived6786 a h
  have h12 : Entails.eval a c9385 := derived9385 a h
  have h13 : Entails.eval a c6810 := derived6810 a h
  have h14 : Entails.eval a c9386 := derived9386 a h
  have h15 : Entails.eval a c7046 := derived7046 a h
  have h16 : Entails.eval a c5823 := h 5822 (by decide)
  have h17 : Entails.eval a c4314 := h 4313 (by decide)
  have h18 : Entails.eval a c6866 := derived6866 a h
  have h19 : Entails.eval a c3857 := h 3856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9388 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨47, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9388 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9387, some c9368, some c6830, some c6846, some c6924, some c6926, some c6888, some c6885, some c7029, some c6794, some c9385, some c6880, some c6811, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9388 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9388 : lratChecker f9388 p9388 = .success := by decide +kernel
theorem unsat9388 : Unsatisfiable (PosFin 65) f9388 := by
  apply lratCheckerSound f9388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9388
  · intro a ha; simp [p9388] at ha; subst a; trivial
  · exact checked9388
theorem derived9388 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9388 := by
  apply localUnsat_implies_entails f9388 [c9367, c9387, c9368, c6830, c6846, c6924, c6926, c6888, c6885, c7029, c6794, c9385, c6880, c6811] c9388 unsat9388 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9387 := derived9387 a h
  have h2 : Entails.eval a c9368 := derived9368 a h
  have h3 : Entails.eval a c6830 := derived6830 a h
  have h4 : Entails.eval a c6846 := derived6846 a h
  have h5 : Entails.eval a c6924 := derived6924 a h
  have h6 : Entails.eval a c6926 := derived6926 a h
  have h7 : Entails.eval a c6888 := derived6888 a h
  have h8 : Entails.eval a c6885 := derived6885 a h
  have h9 : Entails.eval a c7029 := derived7029 a h
  have h10 : Entails.eval a c6794 := derived6794 a h
  have h11 : Entails.eval a c9385 := derived9385 a h
  have h12 : Entails.eval a c6880 := derived6880 a h
  have h13 : Entails.eval a c6811 := derived6811 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9389 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨57, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9389 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9387, some c9376, some c3964, some c6823, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9389 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9389 : lratChecker f9389 p9389 = .success := by decide +kernel
theorem unsat9389 : Unsatisfiable (PosFin 65) f9389 := by
  apply lratCheckerSound f9389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9389
  · intro a ha; simp [p9389] at ha; subst a; trivial
  · exact checked9389
theorem derived9389 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9389 := by
  apply localUnsat_implies_entails f9389 [c9229, c9387, c9376, c3964, c6823] c9389 unsat9389 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9387 := derived9387 a h
  have h2 : Entails.eval a c9376 := derived9376 a h
  have h3 : Entails.eval a c3964 := h 3963 (by decide)
  have h4 : Entails.eval a c6823 := derived6823 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9390 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨62, by decide⟩, true), (⟨47, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9390 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9229, some c9388, some c9389, some c9387, some c6841, some c6835, some c6791, some c6889, some c6803, some c7012, some c6935, some c9310, some c4178, some c4934, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9390 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9390 : lratChecker f9390 p9390 = .success := by decide +kernel
theorem unsat9390 : Unsatisfiable (PosFin 65) f9390 := by
  apply lratCheckerSound f9390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9390
  · intro a ha; simp [p9390] at ha; subst a; trivial
  · exact checked9390
theorem derived9390 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9390 := by
  apply localUnsat_implies_entails f9390 [c9367, c9229, c9388, c9389, c9387, c6841, c6835, c6791, c6889, c6803, c7012, c6935, c9310, c4178, c4934] c9390 unsat9390 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9388 := derived9388 a h
  have h3 : Entails.eval a c9389 := derived9389 a h
  have h4 : Entails.eval a c9387 := derived9387 a h
  have h5 : Entails.eval a c6841 := derived6841 a h
  have h6 : Entails.eval a c6835 := derived6835 a h
  have h7 : Entails.eval a c6791 := derived6791 a h
  have h8 : Entails.eval a c6889 := derived6889 a h
  have h9 : Entails.eval a c6803 := derived6803 a h
  have h10 : Entails.eval a c7012 := derived7012 a h
  have h11 : Entails.eval a c6935 := derived6935 a h
  have h12 : Entails.eval a c9310 := derived9310 a h
  have h13 : Entails.eval a c4178 := h 4177 (by decide)
  have h14 : Entails.eval a c4934 := h 4933 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9391 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨47, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9391 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9388, some c9389, some c9387, some c9390, some c9379, some c6831, some c6847, some c6787, some c6920, some c6805, some c6852, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9391 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9391 : lratChecker f9391 p9391 = .success := by decide +kernel
theorem unsat9391 : Unsatisfiable (PosFin 65) f9391 := by
  apply lratCheckerSound f9391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9391
  · intro a ha; simp [p9391] at ha; subst a; trivial
  · exact checked9391
theorem derived9391 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9391 := by
  apply localUnsat_implies_entails f9391 [c9388, c9389, c9387, c9390, c9379, c6831, c6847, c6787, c6920, c6805, c6852] c9391 unsat9391 (by rfl) a
  have h0 : Entails.eval a c9388 := derived9388 a h
  have h1 : Entails.eval a c9389 := derived9389 a h
  have h2 : Entails.eval a c9387 := derived9387 a h
  have h3 : Entails.eval a c9390 := derived9390 a h
  have h4 : Entails.eval a c9379 := derived9379 a h
  have h5 : Entails.eval a c6831 := derived6831 a h
  have h6 : Entails.eval a c6847 := derived6847 a h
  have h7 : Entails.eval a c6787 := derived6787 a h
  have h8 : Entails.eval a c6920 := derived6920 a h
  have h9 : Entails.eval a c6805 := derived6805 a h
  have h10 : Entails.eval a c6852 := derived6852 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9392 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9392 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9229, some c4316, some c4011, some c4689, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p9392 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9392 : lratChecker f9392 p9392 = .success := by decide +kernel
theorem unsat9392 : Unsatisfiable (PosFin 65) f9392 := by
  apply lratCheckerSound f9392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9392
  · intro a ha; simp [p9392] at ha; subst a; trivial
  · exact checked9392
theorem derived9392 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9392 := by
  apply localUnsat_implies_entails f9392 [c9367, c9229, c4316, c4011, c4689] c9392 unsat9392 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c4316 := h 4315 (by decide)
  have h3 : Entails.eval a c4011 := h 4010 (by decide)
  have h4 : Entails.eval a c4689 := h 4688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9393 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9393 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9387, some c9388, some c9391, some c9392, some c4090, some c4104, some c5856, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9393 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9393 : lratChecker f9393 p9393 = .success := by decide +kernel
theorem unsat9393 : Unsatisfiable (PosFin 65) f9393 := by
  apply lratCheckerSound f9393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9393
  · intro a ha; simp [p9393] at ha; subst a; trivial
  · exact checked9393
theorem derived9393 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9393 := by
  apply localUnsat_implies_entails f9393 [c9229, c9387, c9388, c9391, c9392, c4090, c4104, c5856] c9393 unsat9393 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9387 := derived9387 a h
  have h2 : Entails.eval a c9388 := derived9388 a h
  have h3 : Entails.eval a c9391 := derived9391 a h
  have h4 : Entails.eval a c9392 := derived9392 a h
  have h5 : Entails.eval a c4090 := h 4089 (by decide)
  have h6 : Entails.eval a c4104 := h 4103 (by decide)
  have h7 : Entails.eval a c5856 := h 5855 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9394 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9394 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9229, some c9393, some c9384, some c9389, some c9387, some c3632, some c3524, some c3576, some c4726, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9394 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9394 : lratChecker f9394 p9394 = .success := by decide +kernel
theorem unsat9394 : Unsatisfiable (PosFin 65) f9394 := by
  apply lratCheckerSound f9394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9394
  · intro a ha; simp [p9394] at ha; subst a; trivial
  · exact checked9394
theorem derived9394 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9394 := by
  apply localUnsat_implies_entails f9394 [c9367, c9229, c9393, c9384, c9389, c9387, c3632, c3524, c3576, c4726] c9394 unsat9394 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9393 := derived9393 a h
  have h3 : Entails.eval a c9384 := derived9384 a h
  have h4 : Entails.eval a c9389 := derived9389 a h
  have h5 : Entails.eval a c9387 := derived9387 a h
  have h6 : Entails.eval a c3632 := h 3631 (by decide)
  have h7 : Entails.eval a c3524 := h 3523 (by decide)
  have h8 : Entails.eval a c3576 := h 3575 (by decide)
  have h9 : Entails.eval a c4726 := h 4725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9395 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9395 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9384, some c9389, some c9394, some c6798, some c6985, some c6787, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9395 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9395 : lratChecker f9395 p9395 = .success := by decide +kernel
theorem unsat9395 : Unsatisfiable (PosFin 65) f9395 := by
  apply lratCheckerSound f9395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9395
  · intro a ha; simp [p9395] at ha; subst a; trivial
  · exact checked9395
theorem derived9395 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9395 := by
  apply localUnsat_implies_entails f9395 [c9367, c9384, c9389, c9394, c6798, c6985, c6787] c9395 unsat9395 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9384 := derived9384 a h
  have h2 : Entails.eval a c9389 := derived9389 a h
  have h3 : Entails.eval a c9394 := derived9394 a h
  have h4 : Entails.eval a c6798 := derived6798 a h
  have h5 : Entails.eval a c6985 := derived6985 a h
  have h6 : Entails.eval a c6787 := derived6787 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9396 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9396 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9393, some c9395, some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p9396 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9396 : lratChecker f9396 p9396 = .success := by decide +kernel
theorem unsat9396 : Unsatisfiable (PosFin 65) f9396 := by
  apply lratCheckerSound f9396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9396
  · intro a ha; simp [p9396] at ha; subst a; trivial
  · exact checked9396
theorem derived9396 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9396 := by
  apply localUnsat_implies_entails f9396 [c9393, c9395] c9396 unsat9396 (by rfl) a
  have h0 : Entails.eval a c9393 := derived9393 a h
  have h1 : Entails.eval a c9395 := derived9395 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9397 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9397 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c3539, some c3540, some c9341, some c6193, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p9397 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9397 : lratChecker f9397 p9397 = .success := by decide +kernel
theorem unsat9397 : Unsatisfiable (PosFin 65) f9397 := by
  apply lratCheckerSound f9397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9397
  · intro a ha; simp [p9397] at ha; subst a; trivial
  · exact checked9397
theorem derived9397 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9397 := by
  apply localUnsat_implies_entails f9397 [c9228, c3539, c3540, c9341, c6193] c9397 unsat9397 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c3539 := h 3538 (by decide)
  have h2 : Entails.eval a c3540 := h 3539 (by decide)
  have h3 : Entails.eval a c9341 := derived9341 a h
  have h4 : Entails.eval a c6193 := derived6193 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9398 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9398 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c6981, some c6982, some c5155, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9398 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9398 : lratChecker f9398 p9398 = .success := by decide +kernel
theorem unsat9398 : Unsatisfiable (PosFin 65) f9398 := by
  apply lratCheckerSound f9398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9398
  · intro a ha; simp [p9398] at ha; subst a; trivial
  · exact checked9398
theorem derived9398 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9398 := by
  apply localUnsat_implies_entails f9398 [c9367, c6981, c6982, c5155] c9398 unsat9398 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c6981 := derived6981 a h
  have h2 : Entails.eval a c6982 := derived6982 a h
  have h3 : Entails.eval a c5155 := h 5154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9399 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9399 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9367, some c9228, some c9398, some c9397, some c5892, some c3628, some c9341, some c4565, some c3923, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9399 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9399 : lratChecker f9399 p9399 = .success := by decide +kernel
theorem unsat9399 : Unsatisfiable (PosFin 65) f9399 := by
  apply lratCheckerSound f9399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9399
  · intro a ha; simp [p9399] at ha; subst a; trivial
  · exact checked9399
theorem derived9399 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9399 := by
  apply localUnsat_implies_entails f9399 [c9229, c9367, c9228, c9398, c9397, c5892, c3628, c9341, c4565, c3923] c9399 unsat9399 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9228 := derived9228 a h
  have h3 : Entails.eval a c9398 := derived9398 a h
  have h4 : Entails.eval a c9397 := derived9397 a h
  have h5 : Entails.eval a c5892 := derived5892 a h
  have h6 : Entails.eval a c3628 := h 3627 (by decide)
  have h7 : Entails.eval a c9341 := derived9341 a h
  have h8 : Entails.eval a c4565 := h 4564 (by decide)
  have h9 : Entails.eval a c3923 := h 3922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9400 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨62, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9400 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9229, some c9399, some c6875, some c4400, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9400 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9400 : lratChecker f9400 p9400 = .success := by decide +kernel
theorem unsat9400 : Unsatisfiable (PosFin 65) f9400 := by
  apply lratCheckerSound f9400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9400
  · intro a ha; simp [p9400] at ha; subst a; trivial
  · exact checked9400
theorem derived9400 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9400 := by
  apply localUnsat_implies_entails f9400 [c9367, c9229, c9399, c6875, c4400] c9400 unsat9400 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9399 := derived9399 a h
  have h3 : Entails.eval a c6875 := derived6875 a h
  have h4 : Entails.eval a c4400 := h 4399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9401 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9401 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9396, some c9229, some c9367, some c4409, some c6876, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9401 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9401 : lratChecker f9401 p9401 = .success := by decide +kernel
theorem unsat9401 : Unsatisfiable (PosFin 65) f9401 := by
  apply lratCheckerSound f9401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9401
  · intro a ha; simp [p9401] at ha; subst a; trivial
  · exact checked9401
theorem derived9401 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9401 := by
  apply localUnsat_implies_entails f9401 [c9396, c9229, c9367, c4409, c6876] c9401 unsat9401 (by rfl) a
  have h0 : Entails.eval a c9396 := derived9396 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c4409 := h 4408 (by decide)
  have h4 : Entails.eval a c6876 := derived6876 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9402 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9402 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9401, some c6983, some c6795, some c6784, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9402 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9402 : lratChecker f9402 p9402 = .success := by decide +kernel
theorem unsat9402 : Unsatisfiable (PosFin 65) f9402 := by
  apply lratCheckerSound f9402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9402
  · intro a ha; simp [p9402] at ha; subst a; trivial
  · exact checked9402
theorem derived9402 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9402 := by
  apply localUnsat_implies_entails f9402 [c9367, c9401, c6983, c6795, c6784] c9402 unsat9402 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9401 := derived9401 a h
  have h2 : Entails.eval a c6983 := derived6983 a h
  have h3 : Entails.eval a c6795 := derived6795 a h
  have h4 : Entails.eval a c6784 := derived6784 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9403 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9403 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9228, some c6785, some c3538, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p9403 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9403 : lratChecker f9403 p9403 = .success := by decide +kernel
theorem unsat9403 : Unsatisfiable (PosFin 65) f9403 := by
  apply lratCheckerSound f9403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9403
  · intro a ha; simp [p9403] at ha; subst a; trivial
  · exact checked9403
theorem derived9403 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9403 := by
  apply localUnsat_implies_entails f9403 [c9228, c6785, c3538] c9403 unsat9403 (by rfl) a
  have h0 : Entails.eval a c9228 := derived9228 a h
  have h1 : Entails.eval a c6785 := derived6785 a h
  have h2 : Entails.eval a c3538 := h 3537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9404 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9404 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9396, some c9229, some c9401, some c9402, some c3625, some c9323, some c9403, some c6912, some c5170, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9404 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9404 : lratChecker f9404 p9404 = .success := by decide +kernel
theorem unsat9404 : Unsatisfiable (PosFin 65) f9404 := by
  apply lratCheckerSound f9404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9404
  · intro a ha; simp [p9404] at ha; subst a; trivial
  · exact checked9404
theorem derived9404 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9404 := by
  apply localUnsat_implies_entails f9404 [c9367, c9396, c9229, c9401, c9402, c3625, c9323, c9403, c6912, c5170] c9404 unsat9404 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9396 := derived9396 a h
  have h2 : Entails.eval a c9229 := derived9229 a h
  have h3 : Entails.eval a c9401 := derived9401 a h
  have h4 : Entails.eval a c9402 := derived9402 a h
  have h5 : Entails.eval a c3625 := h 3624 (by decide)
  have h6 : Entails.eval a c9323 := derived9323 a h
  have h7 : Entails.eval a c9403 := derived9403 a h
  have h8 : Entails.eval a c6912 := derived6912 a h
  have h9 : Entails.eval a c5170 := h 5169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9405 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨47, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9405 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9229, some c9228, some c3632, some c4412, some c3524, some c3576, some c9382, some c4689, some c4865, some c4661, some c9122, some c4029, some c5157, some c4016, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9405 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9405 : lratChecker f9405 p9405 = .success := by decide +kernel
theorem unsat9405 : Unsatisfiable (PosFin 65) f9405 := by
  apply lratCheckerSound f9405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9405
  · intro a ha; simp [p9405] at ha; subst a; trivial
  · exact checked9405
theorem derived9405 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9405 := by
  apply localUnsat_implies_entails f9405 [c9367, c9229, c9228, c3632, c4412, c3524, c3576, c9382, c4689, c4865, c4661, c9122, c4029, c5157, c4016] c9405 unsat9405 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9228 := derived9228 a h
  have h3 : Entails.eval a c3632 := h 3631 (by decide)
  have h4 : Entails.eval a c4412 := h 4411 (by decide)
  have h5 : Entails.eval a c3524 := h 3523 (by decide)
  have h6 : Entails.eval a c3576 := h 3575 (by decide)
  have h7 : Entails.eval a c9382 := derived9382 a h
  have h8 : Entails.eval a c4689 := h 4688 (by decide)
  have h9 : Entails.eval a c4865 := h 4864 (by decide)
  have h10 : Entails.eval a c4661 := h 4660 (by decide)
  have h11 : Entails.eval a c9122 := derived9122 a h
  have h12 : Entails.eval a c4029 := h 4028 (by decide)
  have h13 : Entails.eval a c5157 := h 5156 (by decide)
  have h14 : Entails.eval a c4016 := h 4015 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9406 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9406 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9400, some c9405, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9406 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9406 : lratChecker f9406 p9406 = .success := by decide +kernel
theorem unsat9406 : Unsatisfiable (PosFin 65) f9406 := by
  apply lratCheckerSound f9406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9406
  · intro a ha; simp [p9406] at ha; subst a; trivial
  · exact checked9406
theorem derived9406 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9406 := by
  apply localUnsat_implies_entails f9406 [c9400, c9405] c9406 unsat9406 (by rfl) a
  have h0 : Entails.eval a c9400 := derived9400 a h
  have h1 : Entails.eval a c9405 := derived9405 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9407 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9407 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9404, some c9406, some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p9407 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9407 : lratChecker f9407 p9407 = .success := by decide +kernel
theorem unsat9407 : Unsatisfiable (PosFin 65) f9407 := by
  apply lratCheckerSound f9407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9407
  · intro a ha; simp [p9407] at ha; subst a; trivial
  · exact checked9407
theorem derived9407 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9407 := by
  apply localUnsat_implies_entails f9407 [c9404, c9406] c9407 unsat9407 (by rfl) a
  have h0 : Entails.eval a c9404 := derived9404 a h
  have h1 : Entails.eval a c9406 := derived9406 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9408 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9408 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9407, some c9367, some c4689, some c5831, some c5436, some c4726, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9408 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9408 : lratChecker f9408 p9408 = .success := by decide +kernel
theorem unsat9408 : Unsatisfiable (PosFin 65) f9408 := by
  apply lratCheckerSound f9408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9408
  · intro a ha; simp [p9408] at ha; subst a; trivial
  · exact checked9408
theorem derived9408 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9408 := by
  apply localUnsat_implies_entails f9408 [c9229, c9407, c9367, c4689, c5831, c5436, c4726] c9408 unsat9408 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9407 := derived9407 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c4689 := h 4688 (by decide)
  have h4 : Entails.eval a c5831 := h 5830 (by decide)
  have h5 : Entails.eval a c5436 := h 5435 (by decide)
  have h6 : Entails.eval a c4726 := h 4725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9409 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9409 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9407, some c9396, some c9367, some c3946, some c9408, some c9323, some c4377, some c4202, some c4104, some c4489, some c5294, some c5523, some c9304, some c9288, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9409 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9409 : lratChecker f9409 p9409 = .success := by decide +kernel
theorem unsat9409 : Unsatisfiable (PosFin 65) f9409 := by
  apply lratCheckerSound f9409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9409
  · intro a ha; simp [p9409] at ha; subst a; trivial
  · exact checked9409
theorem derived9409 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9409 := by
  apply localUnsat_implies_entails f9409 [c9229, c9407, c9396, c9367, c3946, c9408, c9323, c4377, c4202, c4104, c4489, c5294, c5523, c9304, c9288] c9409 unsat9409 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9407 := derived9407 a h
  have h2 : Entails.eval a c9396 := derived9396 a h
  have h3 : Entails.eval a c9367 := derived9367 a h
  have h4 : Entails.eval a c3946 := h 3945 (by decide)
  have h5 : Entails.eval a c9408 := derived9408 a h
  have h6 : Entails.eval a c9323 := derived9323 a h
  have h7 : Entails.eval a c4377 := h 4376 (by decide)
  have h8 : Entails.eval a c4202 := h 4201 (by decide)
  have h9 : Entails.eval a c4104 := h 4103 (by decide)
  have h10 : Entails.eval a c4489 := h 4488 (by decide)
  have h11 : Entails.eval a c5294 := h 5293 (by decide)
  have h12 : Entails.eval a c5523 := h 5522 (by decide)
  have h13 : Entails.eval a c9304 := derived9304 a h
  have h14 : Entails.eval a c9288 := derived9288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9410 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9410 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9392, some c9409, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9410 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9410 : lratChecker f9410 p9410 = .success := by decide +kernel
theorem unsat9410 : Unsatisfiable (PosFin 65) f9410 := by
  apply lratCheckerSound f9410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9410
  · intro a ha; simp [p9410] at ha; subst a; trivial
  · exact checked9410
theorem derived9410 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9410 := by
  apply localUnsat_implies_entails f9410 [c9407, c9392, c9409] c9410 unsat9410 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9392 := derived9392 a h
  have h2 : Entails.eval a c9409 := derived9409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9411 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨43, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9411 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9396, some c9229, some c4914, some c4256, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9411 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9411 : lratChecker f9411 p9411 = .success := by decide +kernel
theorem unsat9411 : Unsatisfiable (PosFin 65) f9411 := by
  apply lratCheckerSound f9411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9411
  · intro a ha; simp [p9411] at ha; subst a; trivial
  · exact checked9411
theorem derived9411 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9411 := by
  apply localUnsat_implies_entails f9411 [c9407, c9396, c9229, c4914, c4256] c9411 unsat9411 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9396 := derived9396 a h
  have h2 : Entails.eval a c9229 := derived9229 a h
  have h3 : Entails.eval a c4914 := h 4913 (by decide)
  have h4 : Entails.eval a c4256 := h 4255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9412 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9412 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9396, some c9323, some c6856, some c6898, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p9412 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9412 : lratChecker f9412 p9412 = .success := by decide +kernel
theorem unsat9412 : Unsatisfiable (PosFin 65) f9412 := by
  apply lratCheckerSound f9412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9412
  · intro a ha; simp [p9412] at ha; subst a; trivial
  · exact checked9412
theorem derived9412 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9412 := by
  apply localUnsat_implies_entails f9412 [c9396, c9323, c6856, c6898] c9412 unsat9412 (by rfl) a
  have h0 : Entails.eval a c9396 := derived9396 a h
  have h1 : Entails.eval a c9323 := derived9323 a h
  have h2 : Entails.eval a c6856 := derived6856 a h
  have h3 : Entails.eval a c6898 := derived6898 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9413 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9413 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9410, some c9411, some c6832, some c9412, some c6817, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9413 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9413 : lratChecker f9413 p9413 = .success := by decide +kernel
theorem unsat9413 : Unsatisfiable (PosFin 65) f9413 := by
  apply lratCheckerSound f9413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9413
  · intro a ha; simp [p9413] at ha; subst a; trivial
  · exact checked9413
theorem derived9413 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9413 := by
  apply localUnsat_implies_entails f9413 [c9367, c9410, c9411, c6832, c9412, c6817] c9413 unsat9413 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9410 := derived9410 a h
  have h2 : Entails.eval a c9411 := derived9411 a h
  have h3 : Entails.eval a c6832 := derived6832 a h
  have h4 : Entails.eval a c9412 := derived9412 a h
  have h5 : Entails.eval a c6817 := derived6817 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9414 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9414 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9396, some c9367, some c6817, some c6832, some c7045, some c9323, some c6986, some c6898, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p9414 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9414 : lratChecker f9414 p9414 = .success := by decide +kernel
theorem unsat9414 : Unsatisfiable (PosFin 65) f9414 := by
  apply lratCheckerSound f9414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9414
  · intro a ha; simp [p9414] at ha; subst a; trivial
  · exact checked9414
theorem derived9414 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9414 := by
  apply localUnsat_implies_entails f9414 [c9407, c9396, c9367, c6817, c6832, c7045, c9323, c6986, c6898] c9414 unsat9414 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9396 := derived9396 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c6817 := derived6817 a h
  have h4 : Entails.eval a c6832 := derived6832 a h
  have h5 : Entails.eval a c7045 := derived7045 a h
  have h6 : Entails.eval a c9323 := derived9323 a h
  have h7 : Entails.eval a c6986 := derived6986 a h
  have h8 : Entails.eval a c6898 := derived6898 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9415 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨36, by decide⟩, false), (⟨62, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9415 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9396, some c9367, some c9229, some c9407, some c9414, some c4914, some c4045, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p9415 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9415 : lratChecker f9415 p9415 = .success := by decide +kernel
theorem unsat9415 : Unsatisfiable (PosFin 65) f9415 := by
  apply lratCheckerSound f9415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9415
  · intro a ha; simp [p9415] at ha; subst a; trivial
  · exact checked9415
theorem derived9415 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9415 := by
  apply localUnsat_implies_entails f9415 [c9396, c9367, c9229, c9407, c9414, c4914, c4045] c9415 unsat9415 (by rfl) a
  have h0 : Entails.eval a c9396 := derived9396 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9229 := derived9229 a h
  have h3 : Entails.eval a c9407 := derived9407 a h
  have h4 : Entails.eval a c9414 := derived9414 a h
  have h5 : Entails.eval a c4914 := h 4913 (by decide)
  have h6 : Entails.eval a c4045 := h 4044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9416 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨34, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9416 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9410, some c9413, some c9415, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9416 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9416 : lratChecker f9416 p9416 = .success := by decide +kernel
theorem unsat9416 : Unsatisfiable (PosFin 65) f9416 := by
  apply lratCheckerSound f9416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9416
  · intro a ha; simp [p9416] at ha; subst a; trivial
  · exact checked9416
theorem derived9416 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9416 := by
  apply localUnsat_implies_entails f9416 [c9410, c9413, c9415] c9416 unsat9416 (by rfl) a
  have h0 : Entails.eval a c9410 := derived9410 a h
  have h1 : Entails.eval a c9413 := derived9413 a h
  have h2 : Entails.eval a c9415 := derived9415 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9417 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨36, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9417 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9229, some c9367, some c5812, some c4667, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9417 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9417 : lratChecker f9417 p9417 = .success := by decide +kernel
theorem unsat9417 : Unsatisfiable (PosFin 65) f9417 := by
  apply lratCheckerSound f9417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9417
  · intro a ha; simp [p9417] at ha; subst a; trivial
  · exact checked9417
theorem derived9417 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9417 := by
  apply localUnsat_implies_entails f9417 [c9407, c9229, c9367, c5812, c4667] c9417 unsat9417 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c5812 := h 5811 (by decide)
  have h4 : Entails.eval a c4667 := h 4666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9418 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨36, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9418 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9407, some c9410, some c9417, some c6916, some c7045, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9418 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9418 : lratChecker f9418 p9418 = .success := by decide +kernel
theorem unsat9418 : Unsatisfiable (PosFin 65) f9418 := by
  apply lratCheckerSound f9418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9418
  · intro a ha; simp [p9418] at ha; subst a; trivial
  · exact checked9418
theorem derived9418 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9418 := by
  apply localUnsat_implies_entails f9418 [c9367, c9407, c9410, c9417, c6916, c7045] c9418 unsat9418 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9407 := derived9407 a h
  have h2 : Entails.eval a c9410 := derived9410 a h
  have h3 : Entails.eval a c9417 := derived9417 a h
  have h4 : Entails.eval a c6916 := derived6916 a h
  have h5 : Entails.eval a c7045 := derived7045 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9419 : DefaultClause 65 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨36, by decide⟩, true), (⟨34, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9419 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9407, some c6840, some c6916, some c7006, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p9419 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9419 : lratChecker f9419 p9419 = .success := by decide +kernel
theorem unsat9419 : Unsatisfiable (PosFin 65) f9419 := by
  apply lratCheckerSound f9419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9419
  · intro a ha; simp [p9419] at ha; subst a; trivial
  · exact checked9419
theorem derived9419 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9419 := by
  apply localUnsat_implies_entails f9419 [c9367, c9407, c6840, c6916, c7006] c9419 unsat9419 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9407 := derived9407 a h
  have h2 : Entails.eval a c6840 := derived6840 a h
  have h3 : Entails.eval a c6916 := derived6916 a h
  have h4 : Entails.eval a c7006 := derived7006 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9420 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨36, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9420 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9396, some c9229, some c9419, some c4754, some c4070, some c5281, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p9420 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9420 : lratChecker f9420 p9420 = .success := by decide +kernel
theorem unsat9420 : Unsatisfiable (PosFin 65) f9420 := by
  apply lratCheckerSound f9420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9420
  · intro a ha; simp [p9420] at ha; subst a; trivial
  · exact checked9420
theorem derived9420 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9420 := by
  apply localUnsat_implies_entails f9420 [c9407, c9396, c9229, c9419, c4754, c4070, c5281] c9420 unsat9420 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9396 := derived9396 a h
  have h2 : Entails.eval a c9229 := derived9229 a h
  have h3 : Entails.eval a c9419 := derived9419 a h
  have h4 : Entails.eval a c4754 := h 4753 (by decide)
  have h5 : Entails.eval a c4070 := h 4069 (by decide)
  have h6 : Entails.eval a c5281 := h 5280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9421 : DefaultClause 65 := directClause [(⟨34, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9421 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9410, some c9416, some c9418, some c9420, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9421 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9421 : lratChecker f9421 p9421 = .success := by decide +kernel
theorem unsat9421 : Unsatisfiable (PosFin 65) f9421 := by
  apply lratCheckerSound f9421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9421
  · intro a ha; simp [p9421] at ha; subst a; trivial
  · exact checked9421
theorem derived9421 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9421 := by
  apply localUnsat_implies_entails f9421 [c9410, c9416, c9418, c9420] c9421 unsat9421 (by rfl) a
  have h0 : Entails.eval a c9410 := derived9410 a h
  have h1 : Entails.eval a c9416 := derived9416 a h
  have h2 : Entails.eval a c9418 := derived9418 a h
  have h3 : Entails.eval a c9420 := derived9420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9422 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨36, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9422 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9229, some c9396, some c9418, some c9421, some c4132, some c4754, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9422 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9422 : lratChecker f9422 p9422 = .success := by decide +kernel
theorem unsat9422 : Unsatisfiable (PosFin 65) f9422 := by
  apply lratCheckerSound f9422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9422
  · intro a ha; simp [p9422] at ha; subst a; trivial
  · exact checked9422
theorem derived9422 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9422 := by
  apply localUnsat_implies_entails f9422 [c9407, c9229, c9396, c9418, c9421, c4132, c4754] c9422 unsat9422 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9396 := derived9396 a h
  have h3 : Entails.eval a c9418 := derived9418 a h
  have h4 : Entails.eval a c9421 := derived9421 a h
  have h5 : Entails.eval a c4132 := h 4131 (by decide)
  have h6 : Entails.eval a c4754 := h 4753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9423 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9423 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9367, some c9421, some c9410, some c9422, some c6864, some c6916, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9423 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9423 : lratChecker f9423 p9423 = .success := by decide +kernel
theorem unsat9423 : Unsatisfiable (PosFin 65) f9423 := by
  apply lratCheckerSound f9423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9423
  · intro a ha; simp [p9423] at ha; subst a; trivial
  · exact checked9423
theorem derived9423 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9423 := by
  apply localUnsat_implies_entails f9423 [c9407, c9367, c9421, c9410, c9422, c6864, c6916] c9423 unsat9423 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9367 := derived9367 a h
  have h2 : Entails.eval a c9421 := derived9421 a h
  have h3 : Entails.eval a c9410 := derived9410 a h
  have h4 : Entails.eval a c9422 := derived9422 a h
  have h5 : Entails.eval a c6864 := derived6864 a h
  have h6 : Entails.eval a c6916 := derived6916 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9424 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9424 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9229, some c9407, some c9410, some c9421, some c9423, some c6828, some c3994, some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p9424 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9424 : lratChecker f9424 p9424 = .success := by decide +kernel
theorem unsat9424 : Unsatisfiable (PosFin 65) f9424 := by
  apply lratCheckerSound f9424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9424
  · intro a ha; simp [p9424] at ha; subst a; trivial
  · exact checked9424
theorem derived9424 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9424 := by
  apply localUnsat_implies_entails f9424 [c9229, c9407, c9410, c9421, c9423, c6828, c3994] c9424 unsat9424 (by rfl) a
  have h0 : Entails.eval a c9229 := derived9229 a h
  have h1 : Entails.eval a c9407 := derived9407 a h
  have h2 : Entails.eval a c9410 := derived9410 a h
  have h3 : Entails.eval a c9421 := derived9421 a h
  have h4 : Entails.eval a c9423 := derived9423 a h
  have h5 : Entails.eval a c6828 := derived6828 a h
  have h6 : Entails.eval a c3994 := h 3993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9425 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9425 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9424, some c9229, some c9396, some c4005, some c6829, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p9425 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9425 : lratChecker f9425 p9425 = .success := by decide +kernel
theorem unsat9425 : Unsatisfiable (PosFin 65) f9425 := by
  apply lratCheckerSound f9425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9425
  · intro a ha; simp [p9425] at ha; subst a; trivial
  · exact checked9425
theorem derived9425 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9425 := by
  apply localUnsat_implies_entails f9425 [c9407, c9424, c9229, c9396, c4005, c6829] c9425 unsat9425 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9424 := derived9424 a h
  have h2 : Entails.eval a c9229 := derived9229 a h
  have h3 : Entails.eval a c9396 := derived9396 a h
  have h4 : Entails.eval a c4005 := h 4004 (by decide)
  have h5 : Entails.eval a c6829 := derived6829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9426 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9426 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9407, some c9424, some c9367, some c9425, some c6865, some c6917, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p9426 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9426 : lratChecker f9426 p9426 = .success := by decide +kernel
theorem unsat9426 : Unsatisfiable (PosFin 65) f9426 := by
  apply lratCheckerSound f9426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9426
  · intro a ha; simp [p9426] at ha; subst a; trivial
  · exact checked9426
theorem derived9426 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9426 := by
  apply localUnsat_implies_entails f9426 [c9407, c9424, c9367, c9425, c6865, c6917] c9426 unsat9426 (by rfl) a
  have h0 : Entails.eval a c9407 := derived9407 a h
  have h1 : Entails.eval a c9424 := derived9424 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c9425 := derived9425 a h
  have h4 : Entails.eval a c6865 := derived6865 a h
  have h5 : Entails.eval a c6917 := derived6917 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9427 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9427 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9396, some c9229, some c9424, some c9228, some c9407, some c9425, some c9426, some c4145, some c4766, some c4742, some c4487, some c4468, some c4224, some c9386, some c6866, some c5824, some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p9427 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9427 : lratChecker f9427 p9427 = .success := by decide +kernel
theorem unsat9427 : Unsatisfiable (PosFin 65) f9427 := by
  apply lratCheckerSound f9427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9427
  · intro a ha; simp [p9427] at ha; subst a; trivial
  · exact checked9427
theorem derived9427 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9427 := by
  apply localUnsat_implies_entails f9427 [c9396, c9229, c9424, c9228, c9407, c9425, c9426, c4145, c4766, c4742, c4487, c4468, c4224, c9386, c6866, c5824] c9427 unsat9427 (by rfl) a
  have h0 : Entails.eval a c9396 := derived9396 a h
  have h1 : Entails.eval a c9229 := derived9229 a h
  have h2 : Entails.eval a c9424 := derived9424 a h
  have h3 : Entails.eval a c9228 := derived9228 a h
  have h4 : Entails.eval a c9407 := derived9407 a h
  have h5 : Entails.eval a c9425 := derived9425 a h
  have h6 : Entails.eval a c9426 := derived9426 a h
  have h7 : Entails.eval a c4145 := h 4144 (by decide)
  have h8 : Entails.eval a c4766 := h 4765 (by decide)
  have h9 : Entails.eval a c4742 := h 4741 (by decide)
  have h10 : Entails.eval a c4487 := h 4486 (by decide)
  have h11 : Entails.eval a c4468 := h 4467 (by decide)
  have h12 : Entails.eval a c4224 := h 4223 (by decide)
  have h13 : Entails.eval a c9386 := derived9386 a h
  have h14 : Entails.eval a c6866 := derived6866 a h
  have h15 : Entails.eval a c5824 := h 5823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9428 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨54, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9428 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9396, some c9407, some c9229, some c9427, some c4742, some c4197, some c5593, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p9428 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9428 : lratChecker f9428 p9428 = .success := by decide +kernel
theorem unsat9428 : Unsatisfiable (PosFin 65) f9428 := by
  apply lratCheckerSound f9428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9428
  · intro a ha; simp [p9428] at ha; subst a; trivial
  · exact checked9428
theorem derived9428 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9428 := by
  apply localUnsat_implies_entails f9428 [c9396, c9407, c9229, c9427, c4742, c4197, c5593] c9428 unsat9428 (by rfl) a
  have h0 : Entails.eval a c9396 := derived9396 a h
  have h1 : Entails.eval a c9407 := derived9407 a h
  have h2 : Entails.eval a c9229 := derived9229 a h
  have h3 : Entails.eval a c9427 := derived9427 a h
  have h4 : Entails.eval a c4742 := h 4741 (by decide)
  have h5 : Entails.eval a c4197 := h 4196 (by decide)
  have h6 : Entails.eval a c5593 := h 5592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9429 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9429 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9427, some c9396, some c9229, some c3939, some c4058, some c4508, some c9428, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p9429 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9429 : lratChecker f9429 p9429 = .success := by decide +kernel
theorem unsat9429 : Unsatisfiable (PosFin 65) f9429 := by
  apply lratCheckerSound f9429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9429
  · intro a ha; simp [p9429] at ha; subst a; trivial
  · exact checked9429
theorem derived9429 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9429 := by
  apply localUnsat_implies_entails f9429 [c9367, c9427, c9396, c9229, c3939, c4058, c4508, c9428] c9429 unsat9429 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9427 := derived9427 a h
  have h2 : Entails.eval a c9396 := derived9396 a h
  have h3 : Entails.eval a c9229 := derived9229 a h
  have h4 : Entails.eval a c3939 := h 3938 (by decide)
  have h5 : Entails.eval a c4058 := h 4057 (by decide)
  have h6 : Entails.eval a c4508 := h 4507 (by decide)
  have h7 : Entails.eval a c9428 := derived9428 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9430 : DefaultClause 65 := directClause [(⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9430 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9427, some c9424, some c9429, some c6818, some c6911, some c6838, some c6901, some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p9430 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9430 : lratChecker f9430 p9430 = .success := by decide +kernel
theorem unsat9430 : Unsatisfiable (PosFin 65) f9430 := by
  apply lratCheckerSound f9430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9430
  · intro a ha; simp [p9430] at ha; subst a; trivial
  · exact checked9430
theorem derived9430 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9430 := by
  apply localUnsat_implies_entails f9430 [c9367, c9427, c9424, c9429, c6818, c6911, c6838, c6901] c9430 unsat9430 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9427 := derived9427 a h
  have h2 : Entails.eval a c9424 := derived9424 a h
  have h3 : Entails.eval a c9429 := derived9429 a h
  have h4 : Entails.eval a c6818 := derived6818 a h
  have h5 : Entails.eval a c6911 := derived6911 a h
  have h6 : Entails.eval a c6838 := derived6838 a h
  have h7 : Entails.eval a c6901 := derived6901 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9431 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9431 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9367, some c9427, some c9424, some c9407, some c9430, some c6838, some c6948, some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p9431 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9431 : lratChecker f9431 p9431 = .success := by decide +kernel
theorem unsat9431 : Unsatisfiable (PosFin 65) f9431 := by
  apply lratCheckerSound f9431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9431
  · intro a ha; simp [p9431] at ha; subst a; trivial
  · exact checked9431
theorem derived9431 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9431 := by
  apply localUnsat_implies_entails f9431 [c9367, c9427, c9424, c9407, c9430, c6838, c6948] c9431 unsat9431 (by rfl) a
  have h0 : Entails.eval a c9367 := derived9367 a h
  have h1 : Entails.eval a c9427 := derived9427 a h
  have h2 : Entails.eval a c9424 := derived9424 a h
  have h3 : Entails.eval a c9407 := derived9407 a h
  have h4 : Entails.eval a c9430 := derived9430 a h
  have h5 : Entails.eval a c6838 := derived6838 a h
  have h6 : Entails.eval a c6948 := derived6948 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9432 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9432 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9431, some c9427, some c9367, some c9396, some c9229, some c3939, some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p9432 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9432 : lratChecker f9432 p9432 = .success := by decide +kernel
theorem unsat9432 : Unsatisfiable (PosFin 65) f9432 := by
  apply lratCheckerSound f9432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9432
  · intro a ha; simp [p9432] at ha; subst a; trivial
  · exact checked9432
theorem derived9432 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9432 := by
  apply localUnsat_implies_entails f9432 [c9431, c9427, c9367, c9396, c9229, c3939] c9432 unsat9432 (by rfl) a
  have h0 : Entails.eval a c9431 := derived9431 a h
  have h1 : Entails.eval a c9427 := derived9427 a h
  have h2 : Entails.eval a c9367 := derived9367 a h
  have h3 : Entails.eval a c9396 := derived9396 a h
  have h4 : Entails.eval a c9229 := derived9229 a h
  have h5 : Entails.eval a c3939 := h 3938 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9433 : DefaultClause 65 := directClause [] (by decide +kernel) (by decide +kernel)
def f9433 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9431, some c9432, some c9396, some c9430, some c9323]
def p9433 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9433 : lratChecker f9433 p9433 = .success := by decide +kernel
theorem unsat9433 : Unsatisfiable (PosFin 65) f9433 := by
  apply lratCheckerSound f9433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9433
  · intro a ha; simp [p9433] at ha; subst a; trivial
  · exact checked9433
theorem derived9433 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9433 := by
  apply localUnsat_implies_entails f9433 [c9431, c9432, c9396, c9430, c9323] c9433 unsat9433 (by rfl) a
  have h0 : Entails.eval a c9431 := derived9431 a h
  have h1 : Entails.eval a c9432 := derived9432 a h
  have h2 : Entails.eval a c9396 := derived9396 a h
  have h3 : Entails.eval a c9430 := derived9430 a h
  have h4 : Entails.eval a c9323 := derived9323 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9433

end CochromaticTwenty.Certificates.FixedCore1
