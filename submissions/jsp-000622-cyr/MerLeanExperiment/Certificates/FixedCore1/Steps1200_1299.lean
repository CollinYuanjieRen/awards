import MerLeanExperiment.Certificates.FixedCore1.Steps1100_1199

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7081 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨41, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4787, some c4936, some c5602, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7081 : lratChecker f7081 p7081 = .success := by decide +kernel
theorem unsat7081 : Unsatisfiable (PosFin 65) f7081 := by
  apply lratCheckerSound f7081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7081
  · intro a ha; simp [p7081] at ha; subst a; trivial
  · exact checked7081
theorem derived7081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7081 := by
  apply localUnsat_implies_entails f7081 [c4787, c4936, c5602] c7081 unsat7081 (by rfl) a
  have h0 : Entails.eval a c4787 := h 4786 (by decide)
  have h1 : Entails.eval a c4936 := h 4935 (by decide)
  have h2 : Entails.eval a c5602 := h 5601 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7082 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5595, some c5601, some c5598, some c5600, some c7021, some c3733, some c3900, some c6800, some c6796, some c6951, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7082 : lratChecker f7082 p7082 = .success := by decide +kernel
theorem unsat7082 : Unsatisfiable (PosFin 65) f7082 := by
  apply lratCheckerSound f7082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7082
  · intro a ha; simp [p7082] at ha; subst a; trivial
  · exact checked7082
theorem derived7082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7082 := by
  apply localUnsat_implies_entails f7082 [c5595, c5601, c5598, c5600, c7021, c3733, c3900, c6800, c6796, c6951] c7082 unsat7082 (by rfl) a
  have h0 : Entails.eval a c5595 := h 5594 (by decide)
  have h1 : Entails.eval a c5601 := h 5600 (by decide)
  have h2 : Entails.eval a c5598 := h 5597 (by decide)
  have h3 : Entails.eval a c5600 := h 5599 (by decide)
  have h4 : Entails.eval a c7021 := derived7021 a h
  have h5 : Entails.eval a c3733 := h 3732 (by decide)
  have h6 : Entails.eval a c3900 := h 3899 (by decide)
  have h7 : Entails.eval a c6800 := derived6800 a h
  have h8 : Entails.eval a c6796 := derived6796 a h
  have h9 : Entails.eval a c6951 := derived6951 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7083 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨62, by decide⟩, false), (⟨61, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨50, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4933, some c4932, some c4938, some c5592, some c6800, some c6992, some c6951, some c6827, some c6833, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7083 : lratChecker f7083 p7083 = .success := by decide +kernel
theorem unsat7083 : Unsatisfiable (PosFin 65) f7083 := by
  apply lratCheckerSound f7083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7083
  · intro a ha; simp [p7083] at ha; subst a; trivial
  · exact checked7083
theorem derived7083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7083 := by
  apply localUnsat_implies_entails f7083 [c4933, c4932, c4938, c5592, c6800, c6992, c6951, c6827, c6833] c7083 unsat7083 (by rfl) a
  have h0 : Entails.eval a c4933 := h 4932 (by decide)
  have h1 : Entails.eval a c4932 := h 4931 (by decide)
  have h2 : Entails.eval a c4938 := h 4937 (by decide)
  have h3 : Entails.eval a c5592 := h 5591 (by decide)
  have h4 : Entails.eval a c6800 := derived6800 a h
  have h5 : Entails.eval a c6992 := derived6992 a h
  have h6 : Entails.eval a c6951 := derived6951 a h
  have h7 : Entails.eval a c6827 := derived6827 a h
  have h8 : Entails.eval a c6833 := derived6833 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7084 : DefaultClause 65 := directClause [(⟨41, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7077, some c7071, some c7060, some c7081, some c7080, some c7082, some c5569, some c5576, some c5572, some c5581, some c7083, some c4798, some c6601, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7084 : lratChecker f7084 p7084 = .success := by decide +kernel
theorem unsat7084 : Unsatisfiable (PosFin 65) f7084 := by
  apply lratCheckerSound f7084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7084
  · intro a ha; simp [p7084] at ha; subst a; trivial
  · exact checked7084
theorem derived7084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7084 := by
  apply localUnsat_implies_entails f7084 [c7077, c7071, c7060, c7081, c7080, c7082, c5569, c5576, c5572, c5581, c7083, c4798, c6601] c7084 unsat7084 (by rfl) a
  have h0 : Entails.eval a c7077 := derived7077 a h
  have h1 : Entails.eval a c7071 := derived7071 a h
  have h2 : Entails.eval a c7060 := derived7060 a h
  have h3 : Entails.eval a c7081 := derived7081 a h
  have h4 : Entails.eval a c7080 := derived7080 a h
  have h5 : Entails.eval a c7082 := derived7082 a h
  have h6 : Entails.eval a c5569 := h 5568 (by decide)
  have h7 : Entails.eval a c5576 := h 5575 (by decide)
  have h8 : Entails.eval a c5572 := h 5571 (by decide)
  have h9 : Entails.eval a c5581 := h 5580 (by decide)
  have h10 : Entails.eval a c7083 := derived7083 a h
  have h11 : Entails.eval a c4798 := h 4797 (by decide)
  have h12 : Entails.eval a c6601 := derived6601 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7085 : DefaultClause 65 := directClause [(⟨47, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5569, some c5576, some c5572, some c5573, some c5581, some c7083, some c5592, some c5582, some c6608, some c7010, some c6958, some c4648, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7085 : lratChecker f7085 p7085 = .success := by decide +kernel
theorem unsat7085 : Unsatisfiable (PosFin 65) f7085 := by
  apply lratCheckerSound f7085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7085
  · intro a ha; simp [p7085] at ha; subst a; trivial
  · exact checked7085
theorem derived7085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7085 := by
  apply localUnsat_implies_entails f7085 [c5569, c5576, c5572, c5573, c5581, c7083, c5592, c5582, c6608, c7010, c6958, c4648] c7085 unsat7085 (by rfl) a
  have h0 : Entails.eval a c5569 := h 5568 (by decide)
  have h1 : Entails.eval a c5576 := h 5575 (by decide)
  have h2 : Entails.eval a c5572 := h 5571 (by decide)
  have h3 : Entails.eval a c5573 := h 5572 (by decide)
  have h4 : Entails.eval a c5581 := h 5580 (by decide)
  have h5 : Entails.eval a c7083 := derived7083 a h
  have h6 : Entails.eval a c5592 := h 5591 (by decide)
  have h7 : Entails.eval a c5582 := h 5581 (by decide)
  have h8 : Entails.eval a c6608 := derived6608 a h
  have h9 : Entails.eval a c7010 := derived7010 a h
  have h10 : Entails.eval a c6958 := derived6958 a h
  have h11 : Entails.eval a c4648 := h 4647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7086 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨39, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7010, some c7040, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7086 : lratChecker f7086 p7086 = .success := by decide +kernel
theorem unsat7086 : Unsatisfiable (PosFin 65) f7086 := by
  apply lratCheckerSound f7086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7086
  · intro a ha; simp [p7086] at ha; subst a; trivial
  · exact checked7086
theorem derived7086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7086 := by
  apply localUnsat_implies_entails f7086 [c7010, c7040] c7086 unsat7086 (by rfl) a
  have h0 : Entails.eval a c7010 := derived7010 a h
  have h1 : Entails.eval a c7040 := derived7040 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7087 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7084, some c7077, some c7071, some c7060, some c7085, some c5882, some c3731, some c3759, some c7086, some c3890, some c3906, some c3889, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7087 : lratChecker f7087 p7087 = .success := by decide +kernel
theorem unsat7087 : Unsatisfiable (PosFin 65) f7087 := by
  apply lratCheckerSound f7087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7087
  · intro a ha; simp [p7087] at ha; subst a; trivial
  · exact checked7087
theorem derived7087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7087 := by
  apply localUnsat_implies_entails f7087 [c7084, c7077, c7071, c7060, c7085, c5882, c3731, c3759, c7086, c3890, c3906, c3889] c7087 unsat7087 (by rfl) a
  have h0 : Entails.eval a c7084 := derived7084 a h
  have h1 : Entails.eval a c7077 := derived7077 a h
  have h2 : Entails.eval a c7071 := derived7071 a h
  have h3 : Entails.eval a c7060 := derived7060 a h
  have h4 : Entails.eval a c7085 := derived7085 a h
  have h5 : Entails.eval a c5882 := derived5882 a h
  have h6 : Entails.eval a c3731 := h 3730 (by decide)
  have h7 : Entails.eval a c3759 := h 3758 (by decide)
  have h8 : Entails.eval a c7086 := derived7086 a h
  have h9 : Entails.eval a c3890 := h 3889 (by decide)
  have h10 : Entails.eval a c3906 := h 3905 (by decide)
  have h11 : Entails.eval a c3889 := h 3888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7088 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7077, some c7060, some c7087, some c3887, some c5577, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7088 : lratChecker f7088 p7088 = .success := by decide +kernel
theorem unsat7088 : Unsatisfiable (PosFin 65) f7088 := by
  apply lratCheckerSound f7088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7088
  · intro a ha; simp [p7088] at ha; subst a; trivial
  · exact checked7088
theorem derived7088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7088 := by
  apply localUnsat_implies_entails f7088 [c7077, c7060, c7087, c3887, c5577] c7088 unsat7088 (by rfl) a
  have h0 : Entails.eval a c7077 := derived7077 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c7087 := derived7087 a h
  have h3 : Entails.eval a c3887 := h 3886 (by decide)
  have h4 : Entails.eval a c5577 := h 5576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7089 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5468, some c5485, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7089 : lratChecker f7089 p7089 = .success := by decide +kernel
theorem unsat7089 : Unsatisfiable (PosFin 65) f7089 := by
  apply lratCheckerSound f7089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7089
  · intro a ha; simp [p7089] at ha; subst a; trivial
  · exact checked7089
theorem derived7089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7089 := by
  apply localUnsat_implies_entails f7089 [c5468, c5485] c7089 unsat7089 (by rfl) a
  have h0 : Entails.eval a c5468 := h 5467 (by decide)
  have h1 : Entails.eval a c5485 := h 5484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7090 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7088, some c7084, some c7077, some c7071, some c7060, some c5577, some c3826, some c4627, some c4361, some c6611, some c7089, some c7042, some c5779, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7090 : lratChecker f7090 p7090 = .success := by decide +kernel
theorem unsat7090 : Unsatisfiable (PosFin 65) f7090 := by
  apply lratCheckerSound f7090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7090
  · intro a ha; simp [p7090] at ha; subst a; trivial
  · exact checked7090
theorem derived7090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7090 := by
  apply localUnsat_implies_entails f7090 [c7088, c7084, c7077, c7071, c7060, c5577, c3826, c4627, c4361, c6611, c7089, c7042, c5779] c7090 unsat7090 (by rfl) a
  have h0 : Entails.eval a c7088 := derived7088 a h
  have h1 : Entails.eval a c7084 := derived7084 a h
  have h2 : Entails.eval a c7077 := derived7077 a h
  have h3 : Entails.eval a c7071 := derived7071 a h
  have h4 : Entails.eval a c7060 := derived7060 a h
  have h5 : Entails.eval a c5577 := h 5576 (by decide)
  have h6 : Entails.eval a c3826 := h 3825 (by decide)
  have h7 : Entails.eval a c4627 := h 4626 (by decide)
  have h8 : Entails.eval a c4361 := h 4360 (by decide)
  have h9 : Entails.eval a c6611 := derived6611 a h
  have h10 : Entails.eval a c7089 := derived7089 a h
  have h11 : Entails.eval a c7042 := derived7042 a h
  have h12 : Entails.eval a c5779 := h 5778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7091 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c7071, some c7077, some c7084, some c7088, some c7090, some c7078, some c4119, some c6369, some c7079, some c5459, some c5460, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7091 : lratChecker f7091 p7091 = .success := by decide +kernel
theorem unsat7091 : Unsatisfiable (PosFin 65) f7091 := by
  apply lratCheckerSound f7091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7091
  · intro a ha; simp [p7091] at ha; subst a; trivial
  · exact checked7091
theorem derived7091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7091 := by
  apply localUnsat_implies_entails f7091 [c7060, c7071, c7077, c7084, c7088, c7090, c7078, c4119, c6369, c7079, c5459, c5460] c7091 unsat7091 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c7071 := derived7071 a h
  have h2 : Entails.eval a c7077 := derived7077 a h
  have h3 : Entails.eval a c7084 := derived7084 a h
  have h4 : Entails.eval a c7088 := derived7088 a h
  have h5 : Entails.eval a c7090 := derived7090 a h
  have h6 : Entails.eval a c7078 := derived7078 a h
  have h7 : Entails.eval a c4119 := h 4118 (by decide)
  have h8 : Entails.eval a c6369 := derived6369 a h
  have h9 : Entails.eval a c7079 := derived7079 a h
  have h10 : Entails.eval a c5459 := h 5458 (by decide)
  have h11 : Entails.eval a c5460 := h 5459 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7092 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5459, some c5484, some c5481, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7092 : lratChecker f7092 p7092 = .success := by decide +kernel
theorem unsat7092 : Unsatisfiable (PosFin 65) f7092 := by
  apply lratCheckerSound f7092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7092
  · intro a ha; simp [p7092] at ha; subst a; trivial
  · exact checked7092
theorem derived7092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7092 := by
  apply localUnsat_implies_entails f7092 [c5459, c5484, c5481] c7092 unsat7092 (by rfl) a
  have h0 : Entails.eval a c5459 := h 5458 (by decide)
  have h1 : Entails.eval a c5484 := h 5483 (by decide)
  have h2 : Entails.eval a c5481 := h 5480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7093 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c7092, some c6305, some c4583, some c7067, some c4573, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7093 : lratChecker f7093 p7093 = .success := by decide +kernel
theorem unsat7093 : Unsatisfiable (PosFin 65) f7093 := by
  apply lratCheckerSound f7093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7093
  · intro a ha; simp [p7093] at ha; subst a; trivial
  · exact checked7093
theorem derived7093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7093 := by
  apply localUnsat_implies_entails f7093 [c7060, c7092, c6305, c4583, c7067, c4573] c7093 unsat7093 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c7092 := derived7092 a h
  have h2 : Entails.eval a c6305 := derived6305 a h
  have h3 : Entails.eval a c4583 := h 4582 (by decide)
  have h4 : Entails.eval a c7067 := derived7067 a h
  have h5 : Entails.eval a c4573 := h 4572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7094 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7091, some c7060, some c6305, some c4114, some c4498, some c4605, some c4260, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7094 : lratChecker f7094 p7094 = .success := by decide +kernel
theorem unsat7094 : Unsatisfiable (PosFin 65) f7094 := by
  apply lratCheckerSound f7094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7094
  · intro a ha; simp [p7094] at ha; subst a; trivial
  · exact checked7094
theorem derived7094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7094 := by
  apply localUnsat_implies_entails f7094 [c7091, c7060, c6305, c4114, c4498, c4605, c4260] c7094 unsat7094 (by rfl) a
  have h0 : Entails.eval a c7091 := derived7091 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c6305 := derived6305 a h
  have h3 : Entails.eval a c4114 := h 4113 (by decide)
  have h4 : Entails.eval a c4498 := h 4497 (by decide)
  have h5 : Entails.eval a c4605 := h 4604 (by decide)
  have h6 : Entails.eval a c4260 := h 4259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7095 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨52, by decide⟩, false), (⟨42, by decide⟩, true), (⟨50, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5764, some c5773, some c5768, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7095 : lratChecker f7095 p7095 = .success := by decide +kernel
theorem unsat7095 : Unsatisfiable (PosFin 65) f7095 := by
  apply lratCheckerSound f7095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7095
  · intro a ha; simp [p7095] at ha; subst a; trivial
  · exact checked7095
theorem derived7095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7095 := by
  apply localUnsat_implies_entails f7095 [c5764, c5773, c5768] c7095 unsat7095 (by rfl) a
  have h0 : Entails.eval a c5764 := h 5763 (by decide)
  have h1 : Entails.eval a c5773 := h 5772 (by decide)
  have h2 : Entails.eval a c5768 := h 5767 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7096 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4484, some c4602, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7096 : lratChecker f7096 p7096 = .success := by decide +kernel
theorem unsat7096 : Unsatisfiable (PosFin 65) f7096 := by
  apply lratCheckerSound f7096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7096
  · intro a ha; simp [p7096] at ha; subst a; trivial
  · exact checked7096
theorem derived7096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7096 := by
  apply localUnsat_implies_entails f7096 [c4484, c4602] c7096 unsat7096 (by rfl) a
  have h0 : Entails.eval a c4484 := h 4483 (by decide)
  have h1 : Entails.eval a c4602 := h 4601 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7097 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5028, some c5673, some c4382, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p7097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7097 : lratChecker f7097 p7097 = .success := by decide +kernel
theorem unsat7097 : Unsatisfiable (PosFin 65) f7097 := by
  apply lratCheckerSound f7097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7097
  · intro a ha; simp [p7097] at ha; subst a; trivial
  · exact checked7097
theorem derived7097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7097 := by
  apply localUnsat_implies_entails f7097 [c5028, c5673, c4382] c7097 unsat7097 (by rfl) a
  have h0 : Entails.eval a c5028 := h 5027 (by decide)
  have h1 : Entails.eval a c5673 := h 5672 (by decide)
  have h2 : Entails.eval a c4382 := h 4381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7098 : DefaultClause 65 := directClause [(⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7091, some c7060, some c7093, some c7094, some c7095, some c7096, some c7097, some c6369, some c3648, some c5333, some c6304, some c3580, some c5180, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7098 : lratChecker f7098 p7098 = .success := by decide +kernel
theorem unsat7098 : Unsatisfiable (PosFin 65) f7098 := by
  apply lratCheckerSound f7098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7098
  · intro a ha; simp [p7098] at ha; subst a; trivial
  · exact checked7098
theorem derived7098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7098 := by
  apply localUnsat_implies_entails f7098 [c7091, c7060, c7093, c7094, c7095, c7096, c7097, c6369, c3648, c5333, c6304, c3580, c5180] c7098 unsat7098 (by rfl) a
  have h0 : Entails.eval a c7091 := derived7091 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c7093 := derived7093 a h
  have h3 : Entails.eval a c7094 := derived7094 a h
  have h4 : Entails.eval a c7095 := derived7095 a h
  have h5 : Entails.eval a c7096 := derived7096 a h
  have h6 : Entails.eval a c7097 := derived7097 a h
  have h7 : Entails.eval a c6369 := derived6369 a h
  have h8 : Entails.eval a c3648 := h 3647 (by decide)
  have h9 : Entails.eval a c5333 := h 5332 (by decide)
  have h10 : Entails.eval a c6304 := derived6304 a h
  have h11 : Entails.eval a c3580 := h 3579 (by decide)
  have h12 : Entails.eval a c5180 := h 5179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7099 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7098, some c7091, some c7096, some c7097, some c5680, some c4522, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7099 : lratChecker f7099 p7099 = .success := by decide +kernel
theorem unsat7099 : Unsatisfiable (PosFin 65) f7099 := by
  apply lratCheckerSound f7099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7099
  · intro a ha; simp [p7099] at ha; subst a; trivial
  · exact checked7099
theorem derived7099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7099 := by
  apply localUnsat_implies_entails f7099 [c7098, c7091, c7096, c7097, c5680, c4522] c7099 unsat7099 (by rfl) a
  have h0 : Entails.eval a c7098 := derived7098 a h
  have h1 : Entails.eval a c7091 := derived7091 a h
  have h2 : Entails.eval a c7096 := derived7096 a h
  have h3 : Entails.eval a c7097 := derived7097 a h
  have h4 : Entails.eval a c5680 := h 5679 (by decide)
  have h5 : Entails.eval a c4522 := h 4521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7100 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c7099, some c7095, some c5484, some c5478, some c5481, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7100 : lratChecker f7100 p7100 = .success := by decide +kernel
theorem unsat7100 : Unsatisfiable (PosFin 65) f7100 := by
  apply lratCheckerSound f7100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7100
  · intro a ha; simp [p7100] at ha; subst a; trivial
  · exact checked7100
theorem derived7100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7100 := by
  apply localUnsat_implies_entails f7100 [c7060, c7099, c7095, c5484, c5478, c5481] c7100 unsat7100 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c7099 := derived7099 a h
  have h2 : Entails.eval a c7095 := derived7095 a h
  have h3 : Entails.eval a c5484 := h 5483 (by decide)
  have h4 : Entails.eval a c5478 := h 5477 (by decide)
  have h5 : Entails.eval a c5481 := h 5480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7101 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨48, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4368, some c6324, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7101 : lratChecker f7101 p7101 = .success := by decide +kernel
theorem unsat7101 : Unsatisfiable (PosFin 65) f7101 := by
  apply lratCheckerSound f7101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7101
  · intro a ha; simp [p7101] at ha; subst a; trivial
  · exact checked7101
theorem derived7101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7101 := by
  apply localUnsat_implies_entails f7101 [c4368, c6324] c7101 unsat7101 (by rfl) a
  have h0 : Entails.eval a c4368 := h 4367 (by decide)
  have h1 : Entails.eval a c6324 := derived6324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7102 : DefaultClause 65 := directClause [(⟨42, by decide⟩, false), (⟨63, by decide⟩, false), (⟨35, by decide⟩, false), (⟨52, by decide⟩, true), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4583, some c4582, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7102 : lratChecker f7102 p7102 = .success := by decide +kernel
theorem unsat7102 : Unsatisfiable (PosFin 65) f7102 := by
  apply lratCheckerSound f7102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7102
  · intro a ha; simp [p7102] at ha; subst a; trivial
  · exact checked7102
theorem derived7102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7102 := by
  apply localUnsat_implies_entails f7102 [c4583, c4582] c7102 unsat7102 (by rfl) a
  have h0 : Entails.eval a c4583 := h 4582 (by decide)
  have h1 : Entails.eval a c4582 := h 4581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7103 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7091, some c7060, some c7100, some c5585, some c6305, some c3892, some c4498, some c4605, some c4260, some c7101, some c7102, some c5803, some c5777, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7103 : lratChecker f7103 p7103 = .success := by decide +kernel
theorem unsat7103 : Unsatisfiable (PosFin 65) f7103 := by
  apply lratCheckerSound f7103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7103
  · intro a ha; simp [p7103] at ha; subst a; trivial
  · exact checked7103
theorem derived7103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7103 := by
  apply localUnsat_implies_entails f7103 [c7091, c7060, c7100, c5585, c6305, c3892, c4498, c4605, c4260, c7101, c7102, c5803, c5777] c7103 unsat7103 (by rfl) a
  have h0 : Entails.eval a c7091 := derived7091 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c7100 := derived7100 a h
  have h3 : Entails.eval a c5585 := h 5584 (by decide)
  have h4 : Entails.eval a c6305 := derived6305 a h
  have h5 : Entails.eval a c3892 := h 3891 (by decide)
  have h6 : Entails.eval a c4498 := h 4497 (by decide)
  have h7 : Entails.eval a c4605 := h 4604 (by decide)
  have h8 : Entails.eval a c4260 := h 4259 (by decide)
  have h9 : Entails.eval a c7101 := derived7101 a h
  have h10 : Entails.eval a c7102 := derived7102 a h
  have h11 : Entails.eval a c5803 := h 5802 (by decide)
  have h12 : Entails.eval a c5777 := h 5776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7104 : DefaultClause 65 := directClause [(⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨58, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5871, some c3916, some c4326, some c3484, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p7104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7104 : lratChecker f7104 p7104 = .success := by decide +kernel
theorem unsat7104 : Unsatisfiable (PosFin 65) f7104 := by
  apply lratCheckerSound f7104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7104
  · intro a ha; simp [p7104] at ha; subst a; trivial
  · exact checked7104
theorem derived7104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7104 := by
  apply localUnsat_implies_entails f7104 [c5871, c3916, c4326, c3484] c7104 unsat7104 (by rfl) a
  have h0 : Entails.eval a c5871 := h 5870 (by decide)
  have h1 : Entails.eval a c3916 := h 3915 (by decide)
  have h2 : Entails.eval a c4326 := h 4325 (by decide)
  have h3 : Entails.eval a c3484 := h 3483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7105 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨48, by decide⟩, true), (⟨40, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c7104, some c5327, some c4498, some c4430, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7105 : lratChecker f7105 p7105 = .success := by decide +kernel
theorem unsat7105 : Unsatisfiable (PosFin 65) f7105 := by
  apply lratCheckerSound f7105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7105
  · intro a ha; simp [p7105] at ha; subst a; trivial
  · exact checked7105
theorem derived7105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7105 := by
  apply localUnsat_implies_entails f7105 [c7060, c7104, c5327, c4498, c4430] c7105 unsat7105 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c7104 := derived7104 a h
  have h2 : Entails.eval a c5327 := h 5326 (by decide)
  have h3 : Entails.eval a c4498 := h 4497 (by decide)
  have h4 : Entails.eval a c4430 := h 4429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7106 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c4427, some c4434, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7106 : lratChecker f7106 p7106 = .success := by decide +kernel
theorem unsat7106 : Unsatisfiable (PosFin 65) f7106 := by
  apply lratCheckerSound f7106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7106
  · intro a ha; simp [p7106] at ha; subst a; trivial
  · exact checked7106
theorem derived7106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7106 := by
  apply localUnsat_implies_entails f7106 [c7060, c4427, c4434] c7106 unsat7106 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c4427 := h 4426 (by decide)
  have h2 : Entails.eval a c4434 := h 4433 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7107 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5333, some c5317, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7107 : lratChecker f7107 p7107 = .success := by decide +kernel
theorem unsat7107 : Unsatisfiable (PosFin 65) f7107 := by
  apply lratCheckerSound f7107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7107
  · intro a ha; simp [p7107] at ha; subst a; trivial
  · exact checked7107
theorem derived7107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7107 := by
  apply localUnsat_implies_entails f7107 [c5333, c5317] c7107 unsat7107 (by rfl) a
  have h0 : Entails.eval a c5333 := h 5332 (by decide)
  have h1 : Entails.eval a c5317 := h 5316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7108 : DefaultClause 65 := directClause [(⟨46, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7107, some c7106, some c4496, some c4505, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7108 : lratChecker f7108 p7108 = .success := by decide +kernel
theorem unsat7108 : Unsatisfiable (PosFin 65) f7108 := by
  apply lratCheckerSound f7108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7108
  · intro a ha; simp [p7108] at ha; subst a; trivial
  · exact checked7108
theorem derived7108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7108 := by
  apply localUnsat_implies_entails f7108 [c7107, c7106, c4496, c4505] c7108 unsat7108 (by rfl) a
  have h0 : Entails.eval a c7107 := derived7107 a h
  have h1 : Entails.eval a c7106 := derived7106 a h
  have h2 : Entails.eval a c4496 := h 4495 (by decide)
  have h3 : Entails.eval a c4505 := h 4504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7109 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4100, some c5354, some c4119, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7109 : lratChecker f7109 p7109 = .success := by decide +kernel
theorem unsat7109 : Unsatisfiable (PosFin 65) f7109 := by
  apply lratCheckerSound f7109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7109
  · intro a ha; simp [p7109] at ha; subst a; trivial
  · exact checked7109
theorem derived7109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7109 := by
  apply localUnsat_implies_entails f7109 [c4100, c5354, c4119] c7109 unsat7109 (by rfl) a
  have h0 : Entails.eval a c4100 := h 4099 (by decide)
  have h1 : Entails.eval a c5354 := h 5353 (by decide)
  have h2 : Entails.eval a c4119 := h 4118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7110 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7091, some c7103, some c7105, some c7060, some c7109, some c5401, some c4478, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7110 : lratChecker f7110 p7110 = .success := by decide +kernel
theorem unsat7110 : Unsatisfiable (PosFin 65) f7110 := by
  apply lratCheckerSound f7110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7110
  · intro a ha; simp [p7110] at ha; subst a; trivial
  · exact checked7110
theorem derived7110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7110 := by
  apply localUnsat_implies_entails f7110 [c7091, c7103, c7105, c7060, c7109, c5401, c4478] c7110 unsat7110 (by rfl) a
  have h0 : Entails.eval a c7091 := derived7091 a h
  have h1 : Entails.eval a c7103 := derived7103 a h
  have h2 : Entails.eval a c7105 := derived7105 a h
  have h3 : Entails.eval a c7060 := derived7060 a h
  have h4 : Entails.eval a c7109 := derived7109 a h
  have h5 : Entails.eval a c5401 := h 5400 (by decide)
  have h6 : Entails.eval a c4478 := h 4477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7111 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5301, some c5308, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7111 : lratChecker f7111 p7111 = .success := by decide +kernel
theorem unsat7111 : Unsatisfiable (PosFin 65) f7111 := by
  apply lratCheckerSound f7111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7111
  · intro a ha; simp [p7111] at ha; subst a; trivial
  · exact checked7111
theorem derived7111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7111 := by
  apply localUnsat_implies_entails f7111 [c5301, c5308] c7111 unsat7111 (by rfl) a
  have h0 : Entails.eval a c5301 := h 5300 (by decide)
  have h1 : Entails.eval a c5308 := h 5307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7112 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7091, some c7103, some c7105, some c7108, some c6640, some c7111, some c7106, some c7110, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7112 : lratChecker f7112 p7112 = .success := by decide +kernel
theorem unsat7112 : Unsatisfiable (PosFin 65) f7112 := by
  apply lratCheckerSound f7112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7112
  · intro a ha; simp [p7112] at ha; subst a; trivial
  · exact checked7112
theorem derived7112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7112 := by
  apply localUnsat_implies_entails f7112 [c7091, c7103, c7105, c7108, c6640, c7111, c7106, c7110] c7112 unsat7112 (by rfl) a
  have h0 : Entails.eval a c7091 := derived7091 a h
  have h1 : Entails.eval a c7103 := derived7103 a h
  have h2 : Entails.eval a c7105 := derived7105 a h
  have h3 : Entails.eval a c7108 := derived7108 a h
  have h4 : Entails.eval a c6640 := derived6640 a h
  have h5 : Entails.eval a c7111 := derived7111 a h
  have h6 : Entails.eval a c7106 := derived7106 a h
  have h7 : Entails.eval a c7110 := derived7110 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7113 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c3658, some c5402, some c5345, some c3826, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7113 : lratChecker f7113 p7113 = .success := by decide +kernel
theorem unsat7113 : Unsatisfiable (PosFin 65) f7113 := by
  apply lratCheckerSound f7113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7113
  · intro a ha; simp [p7113] at ha; subst a; trivial
  · exact checked7113
theorem derived7113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7113 := by
  apply localUnsat_implies_entails f7113 [c7060, c3658, c5402, c5345, c3826] c7113 unsat7113 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c3658 := h 3657 (by decide)
  have h2 : Entails.eval a c5402 := h 5401 (by decide)
  have h3 : Entails.eval a c5345 := h 5344 (by decide)
  have h4 : Entails.eval a c3826 := h 3825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7114 : DefaultClause 65 := directClause [(⟨48, by decide⟩, true), (⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7112, some c7091, some c7113, some c5318, some c5302, some c5865, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7114 : lratChecker f7114 p7114 = .success := by decide +kernel
theorem unsat7114 : Unsatisfiable (PosFin 65) f7114 := by
  apply lratCheckerSound f7114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7114
  · intro a ha; simp [p7114] at ha; subst a; trivial
  · exact checked7114
theorem derived7114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7114 := by
  apply localUnsat_implies_entails f7114 [c7112, c7091, c7113, c5318, c5302, c5865] c7114 unsat7114 (by rfl) a
  have h0 : Entails.eval a c7112 := derived7112 a h
  have h1 : Entails.eval a c7091 := derived7091 a h
  have h2 : Entails.eval a c7113 := derived7113 a h
  have h3 : Entails.eval a c5318 := h 5317 (by decide)
  have h4 : Entails.eval a c5302 := h 5301 (by decide)
  have h5 : Entails.eval a c5865 := h 5864 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7115 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7060, some c7091, some c7112, some c7114, some c5577, some c4627, some c4603, some c4361, some c5402, some c5302, some c6631, some c4836, some c5029, some c6950, some c6959, some c5009, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7115 : lratChecker f7115 p7115 = .success := by decide +kernel
theorem unsat7115 : Unsatisfiable (PosFin 65) f7115 := by
  apply lratCheckerSound f7115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7115
  · intro a ha; simp [p7115] at ha; subst a; trivial
  · exact checked7115
theorem derived7115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7115 := by
  apply localUnsat_implies_entails f7115 [c7060, c7091, c7112, c7114, c5577, c4627, c4603, c4361, c5402, c5302, c6631, c4836, c5029, c6950, c6959, c5009] c7115 unsat7115 (by rfl) a
  have h0 : Entails.eval a c7060 := derived7060 a h
  have h1 : Entails.eval a c7091 := derived7091 a h
  have h2 : Entails.eval a c7112 := derived7112 a h
  have h3 : Entails.eval a c7114 := derived7114 a h
  have h4 : Entails.eval a c5577 := h 5576 (by decide)
  have h5 : Entails.eval a c4627 := h 4626 (by decide)
  have h6 : Entails.eval a c4603 := h 4602 (by decide)
  have h7 : Entails.eval a c4361 := h 4360 (by decide)
  have h8 : Entails.eval a c5402 := h 5401 (by decide)
  have h9 : Entails.eval a c5302 := h 5301 (by decide)
  have h10 : Entails.eval a c6631 := derived6631 a h
  have h11 : Entails.eval a c4836 := h 4835 (by decide)
  have h12 : Entails.eval a c5029 := h 5028 (by decide)
  have h13 : Entails.eval a c6950 := derived6950 a h
  have h14 : Entails.eval a c6959 := derived6959 a h
  have h15 : Entails.eval a c5009 := h 5008 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7116 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨48, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7115, some c7060, some c4462, some c5509, some c4603, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7116 : lratChecker f7116 p7116 = .success := by decide +kernel
theorem unsat7116 : Unsatisfiable (PosFin 65) f7116 := by
  apply lratCheckerSound f7116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7116
  · intro a ha; simp [p7116] at ha; subst a; trivial
  · exact checked7116
theorem derived7116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7116 := by
  apply localUnsat_implies_entails f7116 [c7115, c7060, c4462, c5509, c4603] c7116 unsat7116 (by rfl) a
  have h0 : Entails.eval a c7115 := derived7115 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c4462 := h 4461 (by decide)
  have h3 : Entails.eval a c5509 := h 5508 (by decide)
  have h4 : Entails.eval a c4603 := h 4602 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7117 : DefaultClause 65 := directClause [(⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7116, some c4605, some c4602, some c4612, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7117 : lratChecker f7117 p7117 = .success := by decide +kernel
theorem unsat7117 : Unsatisfiable (PosFin 65) f7117 := by
  apply lratCheckerSound f7117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7117
  · intro a ha; simp [p7117] at ha; subst a; trivial
  · exact checked7117
theorem derived7117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7117 := by
  apply localUnsat_implies_entails f7117 [c7116, c4605, c4602, c4612] c7117 unsat7117 (by rfl) a
  have h0 : Entails.eval a c7116 := derived7116 a h
  have h1 : Entails.eval a c4605 := h 4604 (by decide)
  have h2 : Entails.eval a c4602 := h 4601 (by decide)
  have h3 : Entails.eval a c4612 := h 4611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7118 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7115, some c7060, some c4466, some c4461, some c4463, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7118 : lratChecker f7118 p7118 = .success := by decide +kernel
theorem unsat7118 : Unsatisfiable (PosFin 65) f7118 := by
  apply lratCheckerSound f7118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7118
  · intro a ha; simp [p7118] at ha; subst a; trivial
  · exact checked7118
theorem derived7118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7118 := by
  apply localUnsat_implies_entails f7118 [c7115, c7060, c4466, c4461, c4463] c7118 unsat7118 (by rfl) a
  have h0 : Entails.eval a c7115 := derived7115 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c4466 := h 4465 (by decide)
  have h3 : Entails.eval a c4461 := h 4460 (by decide)
  have h4 : Entails.eval a c4463 := h 4462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7119 : DefaultClause 65 := directClause [(⟨48, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7115, some c7060, some c7116, some c7118, some c7117, some c5520, some c5515, some c4578, some c5773, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7119 : lratChecker f7119 p7119 = .success := by decide +kernel
theorem unsat7119 : Unsatisfiable (PosFin 65) f7119 := by
  apply lratCheckerSound f7119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7119
  · intro a ha; simp [p7119] at ha; subst a; trivial
  · exact checked7119
theorem derived7119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7119 := by
  apply localUnsat_implies_entails f7119 [c7115, c7060, c7116, c7118, c7117, c5520, c5515, c4578, c5773] c7119 unsat7119 (by rfl) a
  have h0 : Entails.eval a c7115 := derived7115 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c7116 := derived7116 a h
  have h3 : Entails.eval a c7118 := derived7118 a h
  have h4 : Entails.eval a c7117 := derived7117 a h
  have h5 : Entails.eval a c5520 := h 5519 (by decide)
  have h6 : Entails.eval a c5515 := h 5514 (by decide)
  have h7 : Entails.eval a c4578 := h 4577 (by decide)
  have h8 : Entails.eval a c5773 := h 5772 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7120 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨50, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7115, some c7060, some c5520, some c5515, some c5508, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7120 : lratChecker f7120 p7120 = .success := by decide +kernel
theorem unsat7120 : Unsatisfiable (PosFin 65) f7120 := by
  apply lratCheckerSound f7120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7120
  · intro a ha; simp [p7120] at ha; subst a; trivial
  · exact checked7120
theorem derived7120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7120 := by
  apply localUnsat_implies_entails f7120 [c7115, c7060, c5520, c5515, c5508] c7120 unsat7120 (by rfl) a
  have h0 : Entails.eval a c7115 := derived7115 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c5520 := h 5519 (by decide)
  have h3 : Entails.eval a c5515 := h 5514 (by decide)
  have h4 : Entails.eval a c5508 := h 5507 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7121 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨52, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨39, by decide⟩, true), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3559, some c3702, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p7121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7121 : lratChecker f7121 p7121 = .success := by decide +kernel
theorem unsat7121 : Unsatisfiable (PosFin 65) f7121 := by
  apply lratCheckerSound f7121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7121
  · intro a ha; simp [p7121] at ha; subst a; trivial
  · exact checked7121
theorem derived7121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7121 := by
  apply localUnsat_implies_entails f7121 [c3559, c3702] c7121 unsat7121 (by rfl) a
  have h0 : Entails.eval a c3559 := h 3558 (by decide)
  have h1 : Entails.eval a c3702 := h 3701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7122 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨43, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7115, some c7060, some c6369, some c3710, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7122 : lratChecker f7122 p7122 = .success := by decide +kernel
theorem unsat7122 : Unsatisfiable (PosFin 65) f7122 := by
  apply lratCheckerSound f7122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7122
  · intro a ha; simp [p7122] at ha; subst a; trivial
  · exact checked7122
theorem derived7122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7122 := by
  apply localUnsat_implies_entails f7122 [c7115, c7060, c6369, c3710] c7122 unsat7122 (by rfl) a
  have h0 : Entails.eval a c7115 := derived7115 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c6369 := derived6369 a h
  have h3 : Entails.eval a c3710 := h 3709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7123 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7070, some c7105, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p7123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7123 : lratChecker f7123 p7123 = .success := by decide +kernel
theorem unsat7123 : Unsatisfiable (PosFin 65) f7123 := by
  apply lratCheckerSound f7123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7123
  · intro a ha; simp [p7123] at ha; subst a; trivial
  · exact checked7123
theorem derived7123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7123 := by
  apply localUnsat_implies_entails f7123 [c7070, c7105] c7123 unsat7123 (by rfl) a
  have h0 : Entails.eval a c7070 := derived7070 a h
  have h1 : Entails.eval a c7105 := derived7105 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7124 : DefaultClause 65 := directClause [(⟨50, by decide⟩, false), (⟨40, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7119, some c7123, some c7115, some c7060, some c7118, some c7120, some c4484, some c7121, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7124 : lratChecker f7124 p7124 = .success := by decide +kernel
theorem unsat7124 : Unsatisfiable (PosFin 65) f7124 := by
  apply lratCheckerSound f7124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7124
  · intro a ha; simp [p7124] at ha; subst a; trivial
  · exact checked7124
theorem derived7124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7124 := by
  apply localUnsat_implies_entails f7124 [c7119, c7123, c7115, c7060, c7118, c7120, c4484, c7121] c7124 unsat7124 (by rfl) a
  have h0 : Entails.eval a c7119 := derived7119 a h
  have h1 : Entails.eval a c7123 := derived7123 a h
  have h2 : Entails.eval a c7115 := derived7115 a h
  have h3 : Entails.eval a c7060 := derived7060 a h
  have h4 : Entails.eval a c7118 := derived7118 a h
  have h5 : Entails.eval a c7120 := derived7120 a h
  have h6 : Entails.eval a c4484 := h 4483 (by decide)
  have h7 : Entails.eval a c7121 := derived7121 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7125 : DefaultClause 65 := directClause [(⟨40, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7115, some c7060, some c7124, some c4462, some c5509, some c4479, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7125 : lratChecker f7125 p7125 = .success := by decide +kernel
theorem unsat7125 : Unsatisfiable (PosFin 65) f7125 := by
  apply lratCheckerSound f7125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7125
  · intro a ha; simp [p7125] at ha; subst a; trivial
  · exact checked7125
theorem derived7125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7125 := by
  apply localUnsat_implies_entails f7125 [c7115, c7060, c7124, c4462, c5509, c4479] c7125 unsat7125 (by rfl) a
  have h0 : Entails.eval a c7115 := derived7115 a h
  have h1 : Entails.eval a c7060 := derived7060 a h
  have h2 : Entails.eval a c7124 := derived7124 a h
  have h3 : Entails.eval a c4462 := h 4461 (by decide)
  have h4 : Entails.eval a c5509 := h 5508 (by decide)
  have h5 : Entails.eval a c4479 := h 4478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7126 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7119, some c7123, some c7125, some c7076, some c7115, some c7060, some c5509, some c5625, some c3826, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7126 : lratChecker f7126 p7126 = .success := by decide +kernel
theorem unsat7126 : Unsatisfiable (PosFin 65) f7126 := by
  apply lratCheckerSound f7126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7126
  · intro a ha; simp [p7126] at ha; subst a; trivial
  · exact checked7126
theorem derived7126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7126 := by
  apply localUnsat_implies_entails f7126 [c7119, c7123, c7125, c7076, c7115, c7060, c5509, c5625, c3826] c7126 unsat7126 (by rfl) a
  have h0 : Entails.eval a c7119 := derived7119 a h
  have h1 : Entails.eval a c7123 := derived7123 a h
  have h2 : Entails.eval a c7125 := derived7125 a h
  have h3 : Entails.eval a c7076 := derived7076 a h
  have h4 : Entails.eval a c7115 := derived7115 a h
  have h5 : Entails.eval a c7060 := derived7060 a h
  have h6 : Entails.eval a c5509 := h 5508 (by decide)
  have h7 : Entails.eval a c5625 := h 5624 (by decide)
  have h8 : Entails.eval a c3826 := h 3825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7127 : DefaultClause 65 := directClause [(⟨40, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7076, some c7126, some c7118, some c7120, some c3559, some c7122, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7127 : lratChecker f7127 p7127 = .success := by decide +kernel
theorem unsat7127 : Unsatisfiable (PosFin 65) f7127 := by
  apply lratCheckerSound f7127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7127
  · intro a ha; simp [p7127] at ha; subst a; trivial
  · exact checked7127
theorem derived7127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7127 := by
  apply localUnsat_implies_entails f7127 [c7076, c7126, c7118, c7120, c3559, c7122] c7127 unsat7127 (by rfl) a
  have h0 : Entails.eval a c7076 := derived7076 a h
  have h1 : Entails.eval a c7126 := derived7126 a h
  have h2 : Entails.eval a c7118 := derived7118 a h
  have h3 : Entails.eval a c7120 := derived7120 a h
  have h4 : Entails.eval a c3559 := h 3558 (by decide)
  have h5 : Entails.eval a c7122 := derived7122 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7128 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7123, some c7125, some c7127, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7128 : lratChecker f7128 p7128 = .success := by decide +kernel
theorem unsat7128 : Unsatisfiable (PosFin 65) f7128 := by
  apply lratCheckerSound f7128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7128
  · intro a ha; simp [p7128] at ha; subst a; trivial
  · exact checked7128
theorem derived7128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7128 := by
  apply localUnsat_implies_entails f7128 [c7123, c7125, c7127] c7128 unsat7128 (by rfl) a
  have h0 : Entails.eval a c7123 := derived7123 a h
  have h1 : Entails.eval a c7125 := derived7125 a h
  have h2 : Entails.eval a c7127 := derived7127 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7129 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7119, some c7128, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p7129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7129 : lratChecker f7129 p7129 = .success := by decide +kernel
theorem unsat7129 : Unsatisfiable (PosFin 65) f7129 := by
  apply lratCheckerSound f7129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7129
  · intro a ha; simp [p7129] at ha; subst a; trivial
  · exact checked7129
theorem derived7129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7129 := by
  apply localUnsat_implies_entails f7129 [c7119, c7128] c7129 unsat7129 (by rfl) a
  have h0 : Entails.eval a c7119 := derived7119 a h
  have h1 : Entails.eval a c7128 := derived7128 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7130 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1888, some c1889, some c1890, some c1914, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p7130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7130 : lratChecker f7130 p7130 = .success := by decide +kernel
theorem unsat7130 : Unsatisfiable (PosFin 65) f7130 := by
  apply lratCheckerSound f7130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7130
  · intro a ha; simp [p7130] at ha; subst a; trivial
  · exact checked7130
theorem derived7130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7130 := by
  apply localUnsat_implies_entails f7130 [c1888, c1889, c1890, c1914] c7130 unsat7130 (by rfl) a
  have h0 : Entails.eval a c1888 := h 1887 (by decide)
  have h1 : Entails.eval a c1889 := h 1888 (by decide)
  have h2 : Entails.eval a c1890 := h 1889 (by decide)
  have h3 : Entails.eval a c1914 := h 1913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7131 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7130, some c1894, some c1895, some c298, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7131 : lratChecker f7131 p7131 = .success := by decide +kernel
theorem unsat7131 : Unsatisfiable (PosFin 65) f7131 := by
  apply lratCheckerSound f7131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7131
  · intro a ha; simp [p7131] at ha; subst a; trivial
  · exact checked7131
theorem derived7131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7131 := by
  apply localUnsat_implies_entails f7131 [c7130, c1894, c1895, c298] c7131 unsat7131 (by rfl) a
  have h0 : Entails.eval a c7130 := derived7130 a h
  have h1 : Entails.eval a c1894 := h 1893 (by decide)
  have h2 : Entails.eval a c1895 := h 1894 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7132 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c194, some c190, some c192, some c200, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p7132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7132 : lratChecker f7132 p7132 = .success := by decide +kernel
theorem unsat7132 : Unsatisfiable (PosFin 65) f7132 := by
  apply lratCheckerSound f7132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7132
  · intro a ha; simp [p7132] at ha; subst a; trivial
  · exact checked7132
theorem derived7132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7132 := by
  apply localUnsat_implies_entails f7132 [c194, c190, c192, c200] c7132 unsat7132 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7133 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c225, some c228, some c182, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7133 : lratChecker f7133 p7133 = .success := by decide +kernel
theorem unsat7133 : Unsatisfiable (PosFin 65) f7133 := by
  apply lratCheckerSound f7133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7133
  · intro a ha; simp [p7133] at ha; subst a; trivial
  · exact checked7133
theorem derived7133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7133 := by
  apply localUnsat_implies_entails f7133 [c7132, c225, c228, c182] c7133 unsat7133 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c225 := h 224 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7134 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c173, some c1945, some c182, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7134 : lratChecker f7134 p7134 = .success := by decide +kernel
theorem unsat7134 : Unsatisfiable (PosFin 65) f7134 := by
  apply lratCheckerSound f7134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7134
  · intro a ha; simp [p7134] at ha; subst a; trivial
  · exact checked7134
theorem derived7134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7134 := by
  apply localUnsat_implies_entails f7134 [c7132, c173, c1945, c182] c7134 unsat7134 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c173 := h 172 (by decide)
  have h2 : Entails.eval a c1945 := h 1944 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7135 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1891, some c1906, some c1907, some c1897, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p7135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7135 : lratChecker f7135 p7135 = .success := by decide +kernel
theorem unsat7135 : Unsatisfiable (PosFin 65) f7135 := by
  apply lratCheckerSound f7135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7135
  · intro a ha; simp [p7135] at ha; subst a; trivial
  · exact checked7135
theorem derived7135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7135 := by
  apply localUnsat_implies_entails f7135 [c1891, c1906, c1907, c1897] c7135 unsat7135 (by rfl) a
  have h0 : Entails.eval a c1891 := h 1890 (by decide)
  have h1 : Entails.eval a c1906 := h 1905 (by decide)
  have h2 : Entails.eval a c1907 := h 1906 (by decide)
  have h3 : Entails.eval a c1897 := h 1896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7136 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7134, some c7135, some c1949, some c1914, some c183, some c196, some c294, some c290, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7136 : lratChecker f7136 p7136 = .success := by decide +kernel
theorem unsat7136 : Unsatisfiable (PosFin 65) f7136 := by
  apply lratCheckerSound f7136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7136
  · intro a ha; simp [p7136] at ha; subst a; trivial
  · exact checked7136
theorem derived7136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7136 := by
  apply localUnsat_implies_entails f7136 [c7132, c7134, c7135, c1949, c1914, c183, c196, c294, c290] c7136 unsat7136 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c7134 := derived7134 a h
  have h2 : Entails.eval a c7135 := derived7135 a h
  have h3 : Entails.eval a c1949 := h 1948 (by decide)
  have h4 : Entails.eval a c1914 := h 1913 (by decide)
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7137 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7135, some c175, some c176, some c185, some c1898, some c1916, some c291, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7137 : lratChecker f7137 p7137 = .success := by decide +kernel
theorem unsat7137 : Unsatisfiable (PosFin 65) f7137 := by
  apply lratCheckerSound f7137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7137
  · intro a ha; simp [p7137] at ha; subst a; trivial
  · exact checked7137
theorem derived7137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7137 := by
  apply localUnsat_implies_entails f7137 [c7135, c175, c176, c185, c1898, c1916, c291] c7137 unsat7137 (by rfl) a
  have h0 : Entails.eval a c7135 := derived7135 a h
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c1898 := h 1897 (by decide)
  have h5 : Entails.eval a c1916 := h 1915 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7138 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c187, some c208, some c181, some c174, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p7138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7138 : lratChecker f7138 p7138 = .success := by decide +kernel
theorem unsat7138 : Unsatisfiable (PosFin 65) f7138 := by
  apply lratCheckerSound f7138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7138
  · intro a ha; simp [p7138] at ha; subst a; trivial
  · exact checked7138
theorem derived7138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7138 := by
  apply localUnsat_implies_entails f7138 [c187, c208, c181, c174] c7138 unsat7138 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7139 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c293, some c292, some c7138, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7139 : lratChecker f7139 p7139 = .success := by decide +kernel
theorem unsat7139 : Unsatisfiable (PosFin 65) f7139 := by
  apply lratCheckerSound f7139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7139
  · intro a ha; simp [p7139] at ha; subst a; trivial
  · exact checked7139
theorem derived7139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7139 := by
  apply localUnsat_implies_entails f7139 [c293, c292, c7138] c7139 unsat7139 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c7138 := derived7138 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7140 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7139, some c175, some c176, some c297, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7140 : lratChecker f7140 p7140 = .success := by decide +kernel
theorem unsat7140 : Unsatisfiable (PosFin 65) f7140 := by
  apply lratCheckerSound f7140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7140
  · intro a ha; simp [p7140] at ha; subst a; trivial
  · exact checked7140
theorem derived7140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7140 := by
  apply localUnsat_implies_entails f7140 [c7139, c175, c176, c297] c7140 unsat7140 (by rfl) a
  have h0 : Entails.eval a c7139 := derived7139 a h
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7141 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7138, some c1911, some c1915, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7141 : lratChecker f7141 p7141 = .success := by decide +kernel
theorem unsat7141 : Unsatisfiable (PosFin 65) f7141 := by
  apply lratCheckerSound f7141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7141
  · intro a ha; simp [p7141] at ha; subst a; trivial
  · exact checked7141
theorem derived7141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7141 := by
  apply localUnsat_implies_entails f7141 [c7138, c1911, c1915] c7141 unsat7141 (by rfl) a
  have h0 : Entails.eval a c7138 := derived7138 a h
  have h1 : Entails.eval a c1911 := h 1910 (by decide)
  have h2 : Entails.eval a c1915 := h 1914 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7142 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7136, some c7137, some c7139, some c7130, some c7140, some c7141, some c126, some c133, some c2945, some c214, some c326, some c1928, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7142 : lratChecker f7142 p7142 = .success := by decide +kernel
theorem unsat7142 : Unsatisfiable (PosFin 65) f7142 := by
  apply lratCheckerSound f7142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7142
  · intro a ha; simp [p7142] at ha; subst a; trivial
  · exact checked7142
theorem derived7142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7142 := by
  apply localUnsat_implies_entails f7142 [c7136, c7137, c7139, c7130, c7140, c7141, c126, c133, c2945, c214, c326, c1928] c7142 unsat7142 (by rfl) a
  have h0 : Entails.eval a c7136 := derived7136 a h
  have h1 : Entails.eval a c7137 := derived7137 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c7130 := derived7130 a h
  have h4 : Entails.eval a c7140 := derived7140 a h
  have h5 : Entails.eval a c7141 := derived7141 a h
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c2945 := h 2944 (by decide)
  have h9 : Entails.eval a c214 := h 213 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c1928 := h 1927 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7143 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c173, some c177, some c182, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7143 : lratChecker f7143 p7143 = .success := by decide +kernel
theorem unsat7143 : Unsatisfiable (PosFin 65) f7143 := by
  apply lratCheckerSound f7143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7143
  · intro a ha; simp [p7143] at ha; subst a; trivial
  · exact checked7143
theorem derived7143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7143 := by
  apply localUnsat_implies_entails f7143 [c7132, c173, c177, c182] c7143 unsat7143 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c173 := h 172 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7144 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c296, some c301, some c179, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7144 : lratChecker f7144 p7144 = .success := by decide +kernel
theorem unsat7144 : Unsatisfiable (PosFin 65) f7144 := by
  apply lratCheckerSound f7144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7144
  · intro a ha; simp [p7144] at ha; subst a; trivial
  · exact checked7144
theorem derived7144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7144 := by
  apply localUnsat_implies_entails f7144 [c296, c301, c179] c7144 unsat7144 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7145 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7143, some c7135, some c7141, some c1914, some c7131, some c1893, some c1897, some c179, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7145 : lratChecker f7145 p7145 = .success := by decide +kernel
theorem unsat7145 : Unsatisfiable (PosFin 65) f7145 := by
  apply lratCheckerSound f7145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7145
  · intro a ha; simp [p7145] at ha; subst a; trivial
  · exact checked7145
theorem derived7145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7145 := by
  apply localUnsat_implies_entails f7145 [c7132, c7143, c7135, c7141, c1914, c7131, c1893, c1897, c179] c7145 unsat7145 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c7143 := derived7143 a h
  have h2 : Entails.eval a c7135 := derived7135 a h
  have h3 : Entails.eval a c7141 := derived7141 a h
  have h4 : Entails.eval a c1914 := h 1913 (by decide)
  have h5 : Entails.eval a c7131 := derived7131 a h
  have h6 : Entails.eval a c1893 := h 1892 (by decide)
  have h7 : Entails.eval a c1897 := h 1896 (by decide)
  have h8 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7146 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7142, some c7145, some c7137, some c7139, some c7140, some c7130, some c7141, some c953, some c1035, some c2504, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7146 : lratChecker f7146 p7146 = .success := by decide +kernel
theorem unsat7146 : Unsatisfiable (PosFin 65) f7146 := by
  apply lratCheckerSound f7146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7146
  · intro a ha; simp [p7146] at ha; subst a; trivial
  · exact checked7146
theorem derived7146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7146 := by
  apply localUnsat_implies_entails f7146 [c7142, c7145, c7137, c7139, c7140, c7130, c7141, c953, c1035, c2504] c7146 unsat7146 (by rfl) a
  have h0 : Entails.eval a c7142 := derived7142 a h
  have h1 : Entails.eval a c7145 := derived7145 a h
  have h2 : Entails.eval a c7137 := derived7137 a h
  have h3 : Entails.eval a c7139 := derived7139 a h
  have h4 : Entails.eval a c7140 := derived7140 a h
  have h5 : Entails.eval a c7130 := derived7130 a h
  have h6 : Entails.eval a c7141 := derived7141 a h
  have h7 : Entails.eval a c953 := h 952 (by decide)
  have h8 : Entails.eval a c1035 := h 1034 (by decide)
  have h9 : Entails.eval a c2504 := h 2503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7147 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7144, some c7138, some c1944, some c218, some c2507, some c960, some c298, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7147 : lratChecker f7147 p7147 = .success := by decide +kernel
theorem unsat7147 : Unsatisfiable (PosFin 65) f7147 := by
  apply lratCheckerSound f7147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7147
  · intro a ha; simp [p7147] at ha; subst a; trivial
  · exact checked7147
theorem derived7147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7147 := by
  apply localUnsat_implies_entails f7147 [c7144, c7138, c1944, c218, c2507, c960, c298] c7147 unsat7147 (by rfl) a
  have h0 : Entails.eval a c7144 := derived7144 a h
  have h1 : Entails.eval a c7138 := derived7138 a h
  have h2 : Entails.eval a c1944 := h 1943 (by decide)
  have h3 : Entails.eval a c218 := h 217 (by decide)
  have h4 : Entails.eval a c2507 := h 2506 (by decide)
  have h5 : Entails.eval a c960 := h 959 (by decide)
  have h6 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7148 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1930, some c1943, some c1944, some c1936, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p7148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7148 : lratChecker f7148 p7148 = .success := by decide +kernel
theorem unsat7148 : Unsatisfiable (PosFin 65) f7148 := by
  apply lratCheckerSound f7148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7148
  · intro a ha; simp [p7148] at ha; subst a; trivial
  · exact checked7148
theorem derived7148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7148 := by
  apply localUnsat_implies_entails f7148 [c1930, c1943, c1944, c1936] c7148 unsat7148 (by rfl) a
  have h0 : Entails.eval a c1930 := h 1929 (by decide)
  have h1 : Entails.eval a c1943 := h 1942 (by decide)
  have h2 : Entails.eval a c1944 := h 1943 (by decide)
  have h3 : Entails.eval a c1936 := h 1935 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7149 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c218, some c248, some c2473, some c2507, some c2381, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7149 : lratChecker f7149 p7149 = .success := by decide +kernel
theorem unsat7149 : Unsatisfiable (PosFin 65) f7149 := by
  apply lratCheckerSound f7149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7149
  · intro a ha; simp [p7149] at ha; subst a; trivial
  · exact checked7149
theorem derived7149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7149 := by
  apply localUnsat_implies_entails f7149 [c218, c248, c2473, c2507, c2381] c7149 unsat7149 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c2473 := h 2472 (by decide)
  have h3 : Entails.eval a c2507 := h 2506 (by decide)
  have h4 : Entails.eval a c2381 := h 2380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7150 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7143, some c7132, some c7147, some c7148, some c7149, some c204, some c209, some c297, some c203, some c195, some c207, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7150 : lratChecker f7150 p7150 = .success := by decide +kernel
theorem unsat7150 : Unsatisfiable (PosFin 65) f7150 := by
  apply lratCheckerSound f7150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7150
  · intro a ha; simp [p7150] at ha; subst a; trivial
  · exact checked7150
theorem derived7150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7150 := by
  apply localUnsat_implies_entails f7150 [c7143, c7132, c7147, c7148, c7149, c204, c209, c297, c203, c195, c207] c7150 unsat7150 (by rfl) a
  have h0 : Entails.eval a c7143 := derived7143 a h
  have h1 : Entails.eval a c7132 := derived7132 a h
  have h2 : Entails.eval a c7147 := derived7147 a h
  have h3 : Entails.eval a c7148 := derived7148 a h
  have h4 : Entails.eval a c7149 := derived7149 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7151 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1949, some c1950, some c183, some c196, some c294, some c290, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7151 : lratChecker f7151 p7151 = .success := by decide +kernel
theorem unsat7151 : Unsatisfiable (PosFin 65) f7151 := by
  apply lratCheckerSound f7151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7151
  · intro a ha; simp [p7151] at ha; subst a; trivial
  · exact checked7151
theorem derived7151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7151 := by
  apply localUnsat_implies_entails f7151 [c1949, c1950, c183, c196, c294, c290] c7151 unsat7151 (by rfl) a
  have h0 : Entails.eval a c1949 := h 1948 (by decide)
  have h1 : Entails.eval a c1950 := h 1949 (by decide)
  have h2 : Entails.eval a c183 := h 182 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7152 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7144, some c7138, some c180, some c298, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7152 : lratChecker f7152 p7152 = .success := by decide +kernel
theorem unsat7152 : Unsatisfiable (PosFin 65) f7152 := by
  apply lratCheckerSound f7152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7152
  · intro a ha; simp [p7152] at ha; subst a; trivial
  · exact checked7152
theorem derived7152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7152 := by
  apply localUnsat_implies_entails f7152 [c7144, c7138, c180, c298] c7152 unsat7152 (by rfl) a
  have h0 : Entails.eval a c7144 := derived7144 a h
  have h1 : Entails.eval a c7138 := derived7138 a h
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7153 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7150, some c7151, some c7133, some c7143, some c7138, some c180, some c2510, some c123, some c263, some c2391, some c6688, some c6691, some c6700, some c2477, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7153 : lratChecker f7153 p7153 = .success := by decide +kernel
theorem unsat7153 : Unsatisfiable (PosFin 65) f7153 := by
  apply lratCheckerSound f7153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7153
  · intro a ha; simp [p7153] at ha; subst a; trivial
  · exact checked7153
theorem derived7153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7153 := by
  apply localUnsat_implies_entails f7153 [c7132, c7150, c7151, c7133, c7143, c7138, c180, c2510, c123, c263, c2391, c6688, c6691, c6700, c2477] c7153 unsat7153 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c7150 := derived7150 a h
  have h2 : Entails.eval a c7151 := derived7151 a h
  have h3 : Entails.eval a c7133 := derived7133 a h
  have h4 : Entails.eval a c7143 := derived7143 a h
  have h5 : Entails.eval a c7138 := derived7138 a h
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c2510 := h 2509 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c2391 := h 2390 (by decide)
  have h11 : Entails.eval a c6688 := derived6688 a h
  have h12 : Entails.eval a c6691 := derived6691 a h
  have h13 : Entails.eval a c6700 := derived6700 a h
  have h14 : Entails.eval a c2477 := h 2476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7154 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7143, some c7152, some c7153, some c204, some c209, some c297, some c203, some c195, some c207, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7154 : lratChecker f7154 p7154 = .success := by decide +kernel
theorem unsat7154 : Unsatisfiable (PosFin 65) f7154 := by
  apply lratCheckerSound f7154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7154
  · intro a ha; simp [p7154] at ha; subst a; trivial
  · exact checked7154
theorem derived7154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7154 := by
  apply localUnsat_implies_entails f7154 [c7132, c7143, c7152, c7153, c204, c209, c297, c203, c195, c207] c7154 unsat7154 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c7143 := derived7143 a h
  have h2 : Entails.eval a c7152 := derived7152 a h
  have h3 : Entails.eval a c7153 := derived7153 a h
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7155 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨31, by decide⟩, true), (⟨9, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c119, some c143, some c6731, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7155 : lratChecker f7155 p7155 = .success := by decide +kernel
theorem unsat7155 : Unsatisfiable (PosFin 65) f7155 := by
  apply lratCheckerSound f7155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7155
  · intro a ha; simp [p7155] at ha; subst a; trivial
  · exact checked7155
theorem derived7155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7155 := by
  apply localUnsat_implies_entails f7155 [c119, c143, c6731] c7155 unsat7155 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c6731 := derived6731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7156 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7140, some c193, some c178, some c7139, some c217, some c188, some c300, some c7155, some c118, some c6661, some c144, some c113, some c2999, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7156 : lratChecker f7156 p7156 = .success := by decide +kernel
theorem unsat7156 : Unsatisfiable (PosFin 65) f7156 := by
  apply lratCheckerSound f7156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7156
  · intro a ha; simp [p7156] at ha; subst a; trivial
  · exact checked7156
theorem derived7156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7156 := by
  apply localUnsat_implies_entails f7156 [c7140, c193, c178, c7139, c217, c188, c300, c7155, c118, c6661, c144, c113, c2999] c7156 unsat7156 (by rfl) a
  have h0 : Entails.eval a c7140 := derived7140 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c7139 := derived7139 a h
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c7155 := derived7155 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c6661 := derived6661 a h
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c2999 := h 2998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7157 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2516, some c1255, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7157 : lratChecker f7157 p7157 = .success := by decide +kernel
theorem unsat7157 : Unsatisfiable (PosFin 65) f7157 := by
  apply lratCheckerSound f7157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7157
  · intro a ha; simp [p7157] at ha; subst a; trivial
  · exact checked7157
theorem derived7157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7157 := by
  apply localUnsat_implies_entails f7157 [c2516, c1255] c7157 unsat7157 (by rfl) a
  have h0 : Entails.eval a c2516 := h 2515 (by decide)
  have h1 : Entails.eval a c1255 := h 1254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7158 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7154, some c7140, some c7139, some c7148, some c7149, some c191, some c294, some c297, some c193, some c178, some c184, some c7156, some c7157, some c952, some c2501, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7158 : lratChecker f7158 p7158 = .success := by decide +kernel
theorem unsat7158 : Unsatisfiable (PosFin 65) f7158 := by
  apply lratCheckerSound f7158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7158
  · intro a ha; simp [p7158] at ha; subst a; trivial
  · exact checked7158
theorem derived7158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7158 := by
  apply localUnsat_implies_entails f7158 [c7154, c7140, c7139, c7148, c7149, c191, c294, c297, c193, c178, c184, c7156, c7157, c952, c2501] c7158 unsat7158 (by rfl) a
  have h0 : Entails.eval a c7154 := derived7154 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c7148 := derived7148 a h
  have h4 : Entails.eval a c7149 := derived7149 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c7156 := derived7156 a h
  have h12 : Entails.eval a c7157 := derived7157 a h
  have h13 : Entails.eval a c952 := h 951 (by decide)
  have h14 : Entails.eval a c2501 := h 2500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7159 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7140, some c7139, some c191, some c294, some c297, some c193, some c178, some c227, some c344, some c393, some c261, some c2630, some c2601, some c938, some c1830, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7159 : lratChecker f7159 p7159 = .success := by decide +kernel
theorem unsat7159 : Unsatisfiable (PosFin 65) f7159 := by
  apply lratCheckerSound f7159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7159
  · intro a ha; simp [p7159] at ha; subst a; trivial
  · exact checked7159
theorem derived7159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7159 := by
  apply localUnsat_implies_entails f7159 [c7140, c7139, c191, c294, c297, c193, c178, c227, c344, c393, c261, c2630, c2601, c938, c1830] c7159 unsat7159 (by rfl) a
  have h0 : Entails.eval a c7140 := derived7140 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c393 := h 392 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c2630 := h 2629 (by decide)
  have h12 : Entails.eval a c2601 := h 2600 (by decide)
  have h13 : Entails.eval a c938 := h 937 (by decide)
  have h14 : Entails.eval a c1830 := h 1829 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7160 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7154, some c7139, some c7140, some c7158, some c7159, some c7138, some c180, some c123, some c193, some c6688, some c6691, some c6762, some c189, some c299, some c3199, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7160 : lratChecker f7160 p7160 = .success := by decide +kernel
theorem unsat7160 : Unsatisfiable (PosFin 65) f7160 := by
  apply lratCheckerSound f7160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7160
  · intro a ha; simp [p7160] at ha; subst a; trivial
  · exact checked7160
theorem derived7160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7160 := by
  apply localUnsat_implies_entails f7160 [c7154, c7139, c7140, c7158, c7159, c7138, c180, c123, c193, c6688, c6691, c6762, c189, c299, c3199] c7160 unsat7160 (by rfl) a
  have h0 : Entails.eval a c7154 := derived7154 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c7140 := derived7140 a h
  have h3 : Entails.eval a c7158 := derived7158 a h
  have h4 : Entails.eval a c7159 := derived7159 a h
  have h5 : Entails.eval a c7138 := derived7138 a h
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c6688 := derived6688 a h
  have h10 : Entails.eval a c6691 := derived6691 a h
  have h11 : Entails.eval a c6762 := derived6762 a h
  have h12 : Entails.eval a c189 := h 188 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c3199 := h 3198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7161 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, false), (⟨58, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7146, some c7160, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7161 : lratChecker f7161 p7161 = .success := by decide +kernel
theorem unsat7161 : Unsatisfiable (PosFin 65) f7161 := by
  apply lratCheckerSound f7161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7161
  · intro a ha; simp [p7161] at ha; subst a; trivial
  · exact checked7161
theorem derived7161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7161 := by
  apply localUnsat_implies_entails f7161 [c7146, c7160] c7161 unsat7161 (by rfl) a
  have h0 : Entails.eval a c7146 := derived7146 a h
  have h1 : Entails.eval a c7160 := derived7160 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7162 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c938, some c2060, some c2454, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7162 : lratChecker f7162 p7162 = .success := by decide +kernel
theorem unsat7162 : Unsatisfiable (PosFin 65) f7162 := by
  apply lratCheckerSound f7162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7162
  · intro a ha; simp [p7162] at ha; subst a; trivial
  · exact checked7162
theorem derived7162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7162 := by
  apply localUnsat_implies_entails f7162 [c938, c2060, c2454] c7162 unsat7162 (by rfl) a
  have h0 : Entails.eval a c938 := h 937 (by decide)
  have h1 : Entails.eval a c2060 := h 2059 (by decide)
  have h2 : Entails.eval a c2454 := h 2453 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7163 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨32, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c191, some c7139, some c297, some c193, some c184, some c7140, some c217, some c188, some c300, some c186, some c7162, some c144, some c6735, some c6736, some c2913, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7163 : lratChecker f7163 p7163 = .success := by decide +kernel
theorem unsat7163 : Unsatisfiable (PosFin 65) f7163 := by
  apply lratCheckerSound f7163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7163
  · intro a ha; simp [p7163] at ha; subst a; trivial
  · exact checked7163
theorem derived7163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7163 := by
  apply localUnsat_implies_entails f7163 [c191, c7139, c297, c193, c184, c7140, c217, c188, c300, c186, c7162, c144, c6735, c6736, c2913] c7163 unsat7163 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c297 := h 296 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c7140 := derived7140 a h
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c7162 := derived7162 a h
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c6735 := derived6735 a h
  have h13 : Entails.eval a c6736 := derived6736 a h
  have h14 : Entails.eval a c2913 := h 2912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7164 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7157, some c952, some c2501, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7164 : lratChecker f7164 p7164 = .success := by decide +kernel
theorem unsat7164 : Unsatisfiable (PosFin 65) f7164 := by
  apply lratCheckerSound f7164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7164
  · intro a ha; simp [p7164] at ha; subst a; trivial
  · exact checked7164
theorem derived7164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7164 := by
  apply localUnsat_implies_entails f7164 [c7157, c952, c2501] c7164 unsat7164 (by rfl) a
  have h0 : Entails.eval a c7157 := derived7157 a h
  have h1 : Entails.eval a c952 := h 951 (by decide)
  have h2 : Entails.eval a c2501 := h 2500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7165 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c938, some c1383, some c2454, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7165 : lratChecker f7165 p7165 = .success := by decide +kernel
theorem unsat7165 : Unsatisfiable (PosFin 65) f7165 := by
  apply lratCheckerSound f7165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7165
  · intro a ha; simp [p7165] at ha; subst a; trivial
  · exact checked7165
theorem derived7165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7165 := by
  apply localUnsat_implies_entails f7165 [c938, c1383, c2454] c7165 unsat7165 (by rfl) a
  have h0 : Entails.eval a c938 := h 937 (by decide)
  have h1 : Entails.eval a c1383 := h 1382 (by decide)
  have h2 : Entails.eval a c2454 := h 2453 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7166 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7140, some c7139, some c191, some c294, some c297, some c193, some c178, some c7163, some c7164, some c7165, some c1259, some c2272, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7166 : lratChecker f7166 p7166 = .success := by decide +kernel
theorem unsat7166 : Unsatisfiable (PosFin 65) f7166 := by
  apply lratCheckerSound f7166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7166
  · intro a ha; simp [p7166] at ha; subst a; trivial
  · exact checked7166
theorem derived7166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7166 := by
  apply localUnsat_implies_entails f7166 [c7140, c7139, c191, c294, c297, c193, c178, c7163, c7164, c7165, c1259, c2272] c7166 unsat7166 (by rfl) a
  have h0 : Entails.eval a c7140 := derived7140 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c7163 := derived7163 a h
  have h8 : Entails.eval a c7164 := derived7164 a h
  have h9 : Entails.eval a c7165 := derived7165 a h
  have h10 : Entails.eval a c1259 := h 1258 (by decide)
  have h11 : Entails.eval a c2272 := h 2271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7167 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7140, some c7139, some c7166, some c7138, some c218, some c193, some c2278, some c1543, some c189, some c299, some c1266, some c2158, some c2457, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7167 : lratChecker f7167 p7167 = .success := by decide +kernel
theorem unsat7167 : Unsatisfiable (PosFin 65) f7167 := by
  apply lratCheckerSound f7167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7167
  · intro a ha; simp [p7167] at ha; subst a; trivial
  · exact checked7167
theorem derived7167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7167 := by
  apply localUnsat_implies_entails f7167 [c7140, c7139, c7166, c7138, c218, c193, c2278, c1543, c189, c299, c1266, c2158, c2457] c7167 unsat7167 (by rfl) a
  have h0 : Entails.eval a c7140 := derived7140 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c7166 := derived7166 a h
  have h3 : Entails.eval a c7138 := derived7138 a h
  have h4 : Entails.eval a c218 := h 217 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c2278 := h 2277 (by decide)
  have h7 : Entails.eval a c1543 := h 1542 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c1266 := h 1265 (by decide)
  have h11 : Entails.eval a c2158 := h 2157 (by decide)
  have h12 : Entails.eval a c2457 := h 2456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7168 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7140, some c7139, some c7159, some c7138, some c180, some c226, some c343, some c260, some c193, some c2603, some c189, some c299, some c1545, some c2164, some c2628, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7168 : lratChecker f7168 p7168 = .success := by decide +kernel
theorem unsat7168 : Unsatisfiable (PosFin 65) f7168 := by
  apply lratCheckerSound f7168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7168
  · intro a ha; simp [p7168] at ha; subst a; trivial
  · exact checked7168
theorem derived7168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7168 := by
  apply localUnsat_implies_entails f7168 [c7140, c7139, c7159, c7138, c180, c226, c343, c260, c193, c2603, c189, c299, c1545, c2164, c2628] c7168 unsat7168 (by rfl) a
  have h0 : Entails.eval a c7140 := derived7140 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c7159 := derived7159 a h
  have h3 : Entails.eval a c7138 := derived7138 a h
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c2603 := h 2602 (by decide)
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c1545 := h 1544 (by decide)
  have h13 : Entails.eval a c2164 := h 2163 (by decide)
  have h14 : Entails.eval a c2628 := h 2627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7169 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1034, some c1960, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7169 : lratChecker f7169 p7169 = .success := by decide +kernel
theorem unsat7169 : Unsatisfiable (PosFin 65) f7169 := by
  apply lratCheckerSound f7169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7169
  · intro a ha; simp [p7169] at ha; subst a; trivial
  · exact checked7169
theorem derived7169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7169 := by
  apply localUnsat_implies_entails f7169 [c1034, c1960] c7169 unsat7169 (by rfl) a
  have h0 : Entails.eval a c1034 := h 1033 (by decide)
  have h1 : Entails.eval a c1960 := h 1959 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7170 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1255, some c2273, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7170 : lratChecker f7170 p7170 = .success := by decide +kernel
theorem unsat7170 : Unsatisfiable (PosFin 65) f7170 := by
  apply lratCheckerSound f7170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7170
  · intro a ha; simp [p7170] at ha; subst a; trivial
  · exact checked7170
theorem derived7170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7170 := by
  apply localUnsat_implies_entails f7170 [c1255, c2273] c7170 unsat7170 (by rfl) a
  have h0 : Entails.eval a c1255 := h 1254 (by decide)
  have h1 : Entails.eval a c2273 := h 2272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7171 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7168, some c7140, some c7139, some c294, some c297, some c193, some c178, some c7169, some c7170, some c1980, some c2272, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7171 : lratChecker f7171 p7171 = .success := by decide +kernel
theorem unsat7171 : Unsatisfiable (PosFin 65) f7171 := by
  apply lratCheckerSound f7171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7171
  · intro a ha; simp [p7171] at ha; subst a; trivial
  · exact checked7171
theorem derived7171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7171 := by
  apply localUnsat_implies_entails f7171 [c7168, c7140, c7139, c294, c297, c193, c178, c7169, c7170, c1980, c2272] c7171 unsat7171 (by rfl) a
  have h0 : Entails.eval a c7168 := derived7168 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c7169 := derived7169 a h
  have h8 : Entails.eval a c7170 := derived7170 a h
  have h9 : Entails.eval a c1980 := h 1979 (by decide)
  have h10 : Entails.eval a c2272 := h 2271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7172 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7139, some c7140, some c7168, some c7167, some c7171, some c191, some c7138, some c218, some c193, some c2278, some c1989, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7172 : lratChecker f7172 p7172 = .success := by decide +kernel
theorem unsat7172 : Unsatisfiable (PosFin 65) f7172 := by
  apply lratCheckerSound f7172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7172
  · intro a ha; simp [p7172] at ha; subst a; trivial
  · exact checked7172
theorem derived7172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7172 := by
  apply localUnsat_implies_entails f7172 [c7139, c7140, c7168, c7167, c7171, c191, c7138, c218, c193, c2278, c1989] c7172 unsat7172 (by rfl) a
  have h0 : Entails.eval a c7139 := derived7139 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7168 := derived7168 a h
  have h3 : Entails.eval a c7167 := derived7167 a h
  have h4 : Entails.eval a c7171 := derived7171 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c7138 := derived7138 a h
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c2278 := h 2277 (by decide)
  have h10 : Entails.eval a c1989 := h 1988 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7173 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7143, some c7152, some c7132, some c204, some c209, some c297, some c203, some c195, some c207, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7173 : lratChecker f7173 p7173 = .success := by decide +kernel
theorem unsat7173 : Unsatisfiable (PosFin 65) f7173 := by
  apply lratCheckerSound f7173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7173
  · intro a ha; simp [p7173] at ha; subst a; trivial
  · exact checked7173
theorem derived7173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7173 := by
  apply localUnsat_implies_entails f7173 [c7143, c7152, c7132, c204, c209, c297, c203, c195, c207] c7173 unsat7173 (by rfl) a
  have h0 : Entails.eval a c7143 := derived7143 a h
  have h1 : Entails.eval a c7152 := derived7152 a h
  have h2 : Entails.eval a c7132 := derived7132 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c209 := h 208 (by decide)
  have h5 : Entails.eval a c297 := h 296 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7174 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7132, some c7143, some c7173, some c7138, some c180, some c206, some c189, some c186, some c188, some c195, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7174 : lratChecker f7174 p7174 = .success := by decide +kernel
theorem unsat7174 : Unsatisfiable (PosFin 65) f7174 := by
  apply lratCheckerSound f7174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7174
  · intro a ha; simp [p7174] at ha; subst a; trivial
  · exact checked7174
theorem derived7174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7174 := by
  apply localUnsat_implies_entails f7174 [c7132, c7143, c7173, c7138, c180, c206, c189, c186, c188, c195] c7174 unsat7174 (by rfl) a
  have h0 : Entails.eval a c7132 := derived7132 a h
  have h1 : Entails.eval a c7143 := derived7143 a h
  have h2 : Entails.eval a c7173 := derived7173 a h
  have h3 : Entails.eval a c7138 := derived7138 a h
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7175 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7161, some c7172, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7175 : lratChecker f7175 p7175 = .success := by decide +kernel
theorem unsat7175 : Unsatisfiable (PosFin 65) f7175 := by
  apply lratCheckerSound f7175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7175
  · intro a ha; simp [p7175] at ha; subst a; trivial
  · exact checked7175
theorem derived7175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7175 := by
  apply localUnsat_implies_entails f7175 [c7174, c7161, c7172] c7175 unsat7175 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7161 := derived7161 a h
  have h2 : Entails.eval a c7172 := derived7172 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7176 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c938, some c953, some c1243, some c2640, some c2468, some c2283, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7176 : lratChecker f7176 p7176 = .success := by decide +kernel
theorem unsat7176 : Unsatisfiable (PosFin 65) f7176 := by
  apply lratCheckerSound f7176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7176
  · intro a ha; simp [p7176] at ha; subst a; trivial
  · exact checked7176
theorem derived7176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7176 := by
  apply localUnsat_implies_entails f7176 [c938, c953, c1243, c2640, c2468, c2283] c7176 unsat7176 (by rfl) a
  have h0 : Entails.eval a c938 := h 937 (by decide)
  have h1 : Entails.eval a c953 := h 952 (by decide)
  have h2 : Entails.eval a c1243 := h 1242 (by decide)
  have h3 : Entails.eval a c2640 := h 2639 (by decide)
  have h4 : Entails.eval a c2468 := h 2467 (by decide)
  have h5 : Entails.eval a c2283 := h 2282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7177 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c191, some c7139, some c297, some c193, some c184, some c7140, some c178, some c294, some c7159, some c217, some c188, some c300, some c7176, some c1094, some c952, some c1248, some c2637, some c2128, some c2281, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7177 : lratChecker f7177 p7177 = .success := by decide +kernel
theorem unsat7177 : Unsatisfiable (PosFin 65) f7177 := by
  apply lratCheckerSound f7177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7177
  · intro a ha; simp [p7177] at ha; subst a; trivial
  · exact checked7177
theorem derived7177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7177 := by
  apply localUnsat_implies_entails f7177 [c7174, c191, c7139, c297, c193, c184, c7140, c178, c294, c7159, c217, c188, c300, c7176, c1094, c952, c1248, c2637, c2128, c2281] c7177 unsat7177 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c297 := h 296 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c7140 := derived7140 a h
  have h7 : Entails.eval a c178 := h 177 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  have h9 : Entails.eval a c7159 := derived7159 a h
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c7176 := derived7176 a h
  have h14 : Entails.eval a c1094 := h 1093 (by decide)
  have h15 : Entails.eval a c952 := h 951 (by decide)
  have h16 : Entails.eval a c1248 := h 1247 (by decide)
  have h17 : Entails.eval a c2637 := h 2636 (by decide)
  have h18 : Entails.eval a c2128 := h 2127 (by decide)
  have h19 : Entails.eval a c2281 := h 2280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7178 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7140, some c7139, some c191, some c7159, some c294, some c297, some c193, some c178, some c7177, some c7164, some c7165, some c1380, some c937, some c2453, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7178 : lratChecker f7178 p7178 = .success := by decide +kernel
theorem unsat7178 : Unsatisfiable (PosFin 65) f7178 := by
  apply lratCheckerSound f7178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7178
  · intro a ha; simp [p7178] at ha; subst a; trivial
  · exact checked7178
theorem derived7178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7178 := by
  apply localUnsat_implies_entails f7178 [c7174, c7140, c7139, c191, c7159, c294, c297, c193, c178, c7177, c7164, c7165, c1380, c937, c2453] c7178 unsat7178 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c7159 := derived7159 a h
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c7177 := derived7177 a h
  have h10 : Entails.eval a c7164 := derived7164 a h
  have h11 : Entails.eval a c7165 := derived7165 a h
  have h12 : Entails.eval a c1380 := h 1379 (by decide)
  have h13 : Entails.eval a c937 := h 936 (by decide)
  have h14 : Entails.eval a c2453 := h 2452 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7179 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7138, some c193, some c7140, some c7139, some c248, some c2476, some c7149, some c1395, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7179 : lratChecker f7179 p7179 = .success := by decide +kernel
theorem unsat7179 : Unsatisfiable (PosFin 65) f7179 := by
  apply lratCheckerSound f7179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7179
  · intro a ha; simp [p7179] at ha; subst a; trivial
  · exact checked7179
theorem derived7179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7179 := by
  apply localUnsat_implies_entails f7179 [c7174, c7138, c193, c7140, c7139, c248, c2476, c7149, c1395] c7179 unsat7179 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7138 := derived7138 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c7140 := derived7140 a h
  have h4 : Entails.eval a c7139 := derived7139 a h
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c2476 := h 2475 (by decide)
  have h7 : Entails.eval a c7149 := derived7149 a h
  have h8 : Entails.eval a c1395 := h 1394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7180 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7140, some c7139, some c7178, some c7138, some c180, some c193, some c189, some c299, some c186, some c188, some c295, some c202, some c7179, some c343, some c263, some c2095, some c2475, some c2387, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7180 : lratChecker f7180 p7180 = .success := by decide +kernel
theorem unsat7180 : Unsatisfiable (PosFin 65) f7180 := by
  apply lratCheckerSound f7180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7180
  · intro a ha; simp [p7180] at ha; subst a; trivial
  · exact checked7180
theorem derived7180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7180 := by
  apply localUnsat_implies_entails f7180 [c7174, c7140, c7139, c7178, c7138, c180, c193, c189, c299, c186, c188, c295, c202, c7179, c343, c263, c2095, c2475, c2387] c7180 unsat7180 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7140 := derived7140 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c7178 := derived7178 a h
  have h4 : Entails.eval a c7138 := derived7138 a h
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c7179 := derived7179 a h
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c2095 := h 2094 (by decide)
  have h17 : Entails.eval a c2475 := h 2474 (by decide)
  have h18 : Entails.eval a c2387 := h 2386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7180

end CochromaticTwenty.Certificates.FixedCore1
