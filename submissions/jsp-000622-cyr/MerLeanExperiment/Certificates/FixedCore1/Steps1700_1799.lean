import MerLeanExperiment.Certificates.FixedCore1.Steps1600_1699

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7581 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c866, some c871, some c1293, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7581 : lratChecker f7581 p7581 = .success := by decide +kernel
theorem unsat7581 : Unsatisfiable (PosFin 65) f7581 := by
  apply lratCheckerSound f7581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7581
  · intro a ha; simp [p7581] at ha; subst a; trivial
  · exact checked7581
theorem derived7581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7581 := by
  apply localUnsat_implies_entails f7581 [c866, c871, c1293] c7581 unsat7581 (by rfl) a
  have h0 : Entails.eval a c866 := h 865 (by decide)
  have h1 : Entails.eval a c871 := h 870 (by decide)
  have h2 : Entails.eval a c1293 := h 1292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7582 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2022, some c2034, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p7582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7582 : lratChecker f7582 p7582 = .success := by decide +kernel
theorem unsat7582 : Unsatisfiable (PosFin 65) f7582 := by
  apply lratCheckerSound f7582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7582
  · intro a ha; simp [p7582] at ha; subst a; trivial
  · exact checked7582
theorem derived7582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7582 := by
  apply localUnsat_implies_entails f7582 [c2022, c2034] c7582 unsat7582 (by rfl) a
  have h0 : Entails.eval a c2022 := h 2021 (by decide)
  have h1 : Entails.eval a c2034 := h 2033 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7583 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7581, some c7573, some c7582, some c7574, some c2108, some c2110, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7583 : lratChecker f7583 p7583 = .success := by decide +kernel
theorem unsat7583 : Unsatisfiable (PosFin 65) f7583 := by
  apply lratCheckerSound f7583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7583
  · intro a ha; simp [p7583] at ha; subst a; trivial
  · exact checked7583
theorem derived7583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7583 := by
  apply localUnsat_implies_entails f7583 [c7581, c7573, c7582, c7574, c2108, c2110] c7583 unsat7583 (by rfl) a
  have h0 : Entails.eval a c7581 := derived7581 a h
  have h1 : Entails.eval a c7573 := derived7573 a h
  have h2 : Entails.eval a c7582 := derived7582 a h
  have h3 : Entails.eval a c7574 := derived7574 a h
  have h4 : Entails.eval a c2108 := h 2107 (by decide)
  have h5 : Entails.eval a c2110 := h 2109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7584 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7576, some c7569, some c925, some c929, some c1002, some c716, some c1440, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7584 : lratChecker f7584 p7584 = .success := by decide +kernel
theorem unsat7584 : Unsatisfiable (PosFin 65) f7584 := by
  apply lratCheckerSound f7584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7584
  · intro a ha; simp [p7584] at ha; subst a; trivial
  · exact checked7584
theorem derived7584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7584 := by
  apply localUnsat_implies_entails f7584 [c7576, c7569, c925, c929, c1002, c716, c1440] c7584 unsat7584 (by rfl) a
  have h0 : Entails.eval a c7576 := derived7576 a h
  have h1 : Entails.eval a c7569 := derived7569 a h
  have h2 : Entails.eval a c925 := h 924 (by decide)
  have h3 : Entails.eval a c929 := h 928 (by decide)
  have h4 : Entails.eval a c1002 := h 1001 (by decide)
  have h5 : Entails.eval a c716 := h 715 (by decide)
  have h6 : Entails.eval a c1440 := h 1439 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7585 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1935, some c1941, some c1955, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7585 : lratChecker f7585 p7585 = .success := by decide +kernel
theorem unsat7585 : Unsatisfiable (PosFin 65) f7585 := by
  apply lratCheckerSound f7585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7585
  · intro a ha; simp [p7585] at ha; subst a; trivial
  · exact checked7585
theorem derived7585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7585 := by
  apply localUnsat_implies_entails f7585 [c1935, c1941, c1955] c7585 unsat7585 (by rfl) a
  have h0 : Entails.eval a c1935 := h 1934 (by decide)
  have h1 : Entails.eval a c1941 := h 1940 (by decide)
  have h2 : Entails.eval a c1955 := h 1954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7586 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2189, some c1346, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7586 : lratChecker f7586 p7586 = .success := by decide +kernel
theorem unsat7586 : Unsatisfiable (PosFin 65) f7586 := by
  apply lratCheckerSound f7586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7586
  · intro a ha; simp [p7586] at ha; subst a; trivial
  · exact checked7586
theorem derived7586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7586 := by
  apply localUnsat_implies_entails f7586 [c2189, c1346] c7586 unsat7586 (by rfl) a
  have h0 : Entails.eval a c2189 := h 2188 (by decide)
  have h1 : Entails.eval a c1346 := h 1345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7587 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7571, some c7569, some c7583, some c7576, some c7584, some c7586, some c1440, some c698, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7587 : lratChecker f7587 p7587 = .success := by decide +kernel
theorem unsat7587 : Unsatisfiable (PosFin 65) f7587 := by
  apply lratCheckerSound f7587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7587
  · intro a ha; simp [p7587] at ha; subst a; trivial
  · exact checked7587
theorem derived7587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7587 := by
  apply localUnsat_implies_entails f7587 [c7571, c7569, c7583, c7576, c7584, c7586, c1440, c698] c7587 unsat7587 (by rfl) a
  have h0 : Entails.eval a c7571 := derived7571 a h
  have h1 : Entails.eval a c7569 := derived7569 a h
  have h2 : Entails.eval a c7583 := derived7583 a h
  have h3 : Entails.eval a c7576 := derived7576 a h
  have h4 : Entails.eval a c7584 := derived7584 a h
  have h5 : Entails.eval a c7586 := derived7586 a h
  have h6 : Entails.eval a c1440 := h 1439 (by decide)
  have h7 : Entails.eval a c698 := h 697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7588 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c890, some c887, some c870, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7588 : lratChecker f7588 p7588 = .success := by decide +kernel
theorem unsat7588 : Unsatisfiable (PosFin 65) f7588 := by
  apply lratCheckerSound f7588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7588
  · intro a ha; simp [p7588] at ha; subst a; trivial
  · exact checked7588
theorem derived7588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7588 := by
  apply localUnsat_implies_entails f7588 [c890, c887, c870] c7588 unsat7588 (by rfl) a
  have h0 : Entails.eval a c890 := h 889 (by decide)
  have h1 : Entails.eval a c887 := h 886 (by decide)
  have h2 : Entails.eval a c870 := h 869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7589 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c925, some c929, some c923, some c926, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7589 : lratChecker f7589 p7589 = .success := by decide +kernel
theorem unsat7589 : Unsatisfiable (PosFin 65) f7589 := by
  apply lratCheckerSound f7589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7589
  · intro a ha; simp [p7589] at ha; subst a; trivial
  · exact checked7589
theorem derived7589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7589 := by
  apply localUnsat_implies_entails f7589 [c925, c929, c923, c926] c7589 unsat7589 (by rfl) a
  have h0 : Entails.eval a c925 := h 924 (by decide)
  have h1 : Entails.eval a c929 := h 928 (by decide)
  have h2 : Entails.eval a c923 := h 922 (by decide)
  have h3 : Entails.eval a c926 := h 925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7590 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2599, some c2594, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7590 : lratChecker f7590 p7590 = .success := by decide +kernel
theorem unsat7590 : Unsatisfiable (PosFin 65) f7590 := by
  apply lratCheckerSound f7590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7590
  · intro a ha; simp [p7590] at ha; subst a; trivial
  · exact checked7590
theorem derived7590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7590 := by
  apply localUnsat_implies_entails f7590 [c2599, c2594] c7590 unsat7590 (by rfl) a
  have h0 : Entails.eval a c2599 := h 2598 (by decide)
  have h1 : Entails.eval a c2594 := h 2593 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7591 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7587, some c7571, some c7569, some c7588, some c7589, some c7130, some c1367, some c1362, some c1359, some c1340, some c7502, some c1355, some c1446, some c7590, some c2104, some c2115, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7591 : lratChecker f7591 p7591 = .success := by decide +kernel
theorem unsat7591 : Unsatisfiable (PosFin 65) f7591 := by
  apply lratCheckerSound f7591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7591
  · intro a ha; simp [p7591] at ha; subst a; trivial
  · exact checked7591
theorem derived7591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7591 := by
  apply localUnsat_implies_entails f7591 [c7587, c7571, c7569, c7588, c7589, c7130, c1367, c1362, c1359, c1340, c7502, c1355, c1446, c7590, c2104, c2115] c7591 unsat7591 (by rfl) a
  have h0 : Entails.eval a c7587 := derived7587 a h
  have h1 : Entails.eval a c7571 := derived7571 a h
  have h2 : Entails.eval a c7569 := derived7569 a h
  have h3 : Entails.eval a c7588 := derived7588 a h
  have h4 : Entails.eval a c7589 := derived7589 a h
  have h5 : Entails.eval a c7130 := derived7130 a h
  have h6 : Entails.eval a c1367 := h 1366 (by decide)
  have h7 : Entails.eval a c1362 := h 1361 (by decide)
  have h8 : Entails.eval a c1359 := h 1358 (by decide)
  have h9 : Entails.eval a c1340 := h 1339 (by decide)
  have h10 : Entails.eval a c7502 := derived7502 a h
  have h11 : Entails.eval a c1355 := h 1354 (by decide)
  have h12 : Entails.eval a c1446 := h 1445 (by decide)
  have h13 : Entails.eval a c7590 := derived7590 a h
  have h14 : Entails.eval a c2104 := h 2103 (by decide)
  have h15 : Entails.eval a c2115 := h 2114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7592 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c889, some c890, some c878, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7592 : lratChecker f7592 p7592 = .success := by decide +kernel
theorem unsat7592 : Unsatisfiable (PosFin 65) f7592 := by
  apply lratCheckerSound f7592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7592
  · intro a ha; simp [p7592] at ha; subst a; trivial
  · exact checked7592
theorem derived7592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7592 := by
  apply localUnsat_implies_entails f7592 [c889, c890, c878] c7592 unsat7592 (by rfl) a
  have h0 : Entails.eval a c889 := h 888 (by decide)
  have h1 : Entails.eval a c890 := h 889 (by decide)
  have h2 : Entails.eval a c878 := h 877 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7593 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7587, some c7569, some c7571, some c7592, some c7589, some c7591, some c7130, some c1367, some c1340, some c7512, some c2344, some c1155, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7593 : lratChecker f7593 p7593 = .success := by decide +kernel
theorem unsat7593 : Unsatisfiable (PosFin 65) f7593 := by
  apply lratCheckerSound f7593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7593
  · intro a ha; simp [p7593] at ha; subst a; trivial
  · exact checked7593
theorem derived7593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7593 := by
  apply localUnsat_implies_entails f7593 [c7587, c7569, c7571, c7592, c7589, c7591, c7130, c1367, c1340, c7512, c2344, c1155] c7593 unsat7593 (by rfl) a
  have h0 : Entails.eval a c7587 := derived7587 a h
  have h1 : Entails.eval a c7569 := derived7569 a h
  have h2 : Entails.eval a c7571 := derived7571 a h
  have h3 : Entails.eval a c7592 := derived7592 a h
  have h4 : Entails.eval a c7589 := derived7589 a h
  have h5 : Entails.eval a c7591 := derived7591 a h
  have h6 : Entails.eval a c7130 := derived7130 a h
  have h7 : Entails.eval a c1367 := h 1366 (by decide)
  have h8 : Entails.eval a c1340 := h 1339 (by decide)
  have h9 : Entails.eval a c7512 := derived7512 a h
  have h10 : Entails.eval a c2344 := h 2343 (by decide)
  have h11 : Entails.eval a c1155 := h 1154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7594 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c925, some c929, some c7508, some c716, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7594 : lratChecker f7594 p7594 = .success := by decide +kernel
theorem unsat7594 : Unsatisfiable (PosFin 65) f7594 := by
  apply lratCheckerSound f7594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7594
  · intro a ha; simp [p7594] at ha; subst a; trivial
  · exact checked7594
theorem derived7594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7594 := by
  apply localUnsat_implies_entails f7594 [c925, c929, c7508, c716] c7594 unsat7594 (by rfl) a
  have h0 : Entails.eval a c925 := h 924 (by decide)
  have h1 : Entails.eval a c929 := h 928 (by decide)
  have h2 : Entails.eval a c7508 := derived7508 a h
  have h3 : Entails.eval a c716 := h 715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7595 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7571, some c7592, some c7587, some c7593, some c7594, some c7130, some c1367, some c1362, some c1359, some c1340, some c7502, some c1355, some c1439, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7595 : lratChecker f7595 p7595 = .success := by decide +kernel
theorem unsat7595 : Unsatisfiable (PosFin 65) f7595 := by
  apply lratCheckerSound f7595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7595
  · intro a ha; simp [p7595] at ha; subst a; trivial
  · exact checked7595
theorem derived7595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7595 := by
  apply localUnsat_implies_entails f7595 [c7569, c7571, c7592, c7587, c7593, c7594, c7130, c1367, c1362, c1359, c1340, c7502, c1355, c1439] c7595 unsat7595 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7571 := derived7571 a h
  have h2 : Entails.eval a c7592 := derived7592 a h
  have h3 : Entails.eval a c7587 := derived7587 a h
  have h4 : Entails.eval a c7593 := derived7593 a h
  have h5 : Entails.eval a c7594 := derived7594 a h
  have h6 : Entails.eval a c7130 := derived7130 a h
  have h7 : Entails.eval a c1367 := h 1366 (by decide)
  have h8 : Entails.eval a c1362 := h 1361 (by decide)
  have h9 : Entails.eval a c1359 := h 1358 (by decide)
  have h10 : Entails.eval a c1340 := h 1339 (by decide)
  have h11 : Entails.eval a c7502 := derived7502 a h
  have h12 : Entails.eval a c1355 := h 1354 (by decide)
  have h13 : Entails.eval a c1439 := h 1438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7596 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1367, some c1918, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7596 : lratChecker f7596 p7596 = .success := by decide +kernel
theorem unsat7596 : Unsatisfiable (PosFin 65) f7596 := by
  apply lratCheckerSound f7596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7596
  · intro a ha; simp [p7596] at ha; subst a; trivial
  · exact checked7596
theorem derived7596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7596 := by
  apply localUnsat_implies_entails f7596 [c1367, c1918] c7596 unsat7596 (by rfl) a
  have h0 : Entails.eval a c1367 := h 1366 (by decide)
  have h1 : Entails.eval a c1918 := h 1917 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7597 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1362, some c1347, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7597 : lratChecker f7597 p7597 = .success := by decide +kernel
theorem unsat7597 : Unsatisfiable (PosFin 65) f7597 := by
  apply lratCheckerSound f7597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7597
  · intro a ha; simp [p7597] at ha; subst a; trivial
  · exact checked7597
theorem derived7597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7597 := by
  apply localUnsat_implies_entails f7597 [c1362, c1347] c7597 unsat7597 (by rfl) a
  have h0 : Entails.eval a c1362 := h 1361 (by decide)
  have h1 : Entails.eval a c1347 := h 1346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7598 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7596, some c7597, some c1921, some c1897, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7598 : lratChecker f7598 p7598 = .success := by decide +kernel
theorem unsat7598 : Unsatisfiable (PosFin 65) f7598 := by
  apply lratCheckerSound f7598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7598
  · intro a ha; simp [p7598] at ha; subst a; trivial
  · exact checked7598
theorem derived7598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7598 := by
  apply localUnsat_implies_entails f7598 [c7596, c7597, c1921, c1897] c7598 unsat7598 (by rfl) a
  have h0 : Entails.eval a c7596 := derived7596 a h
  have h1 : Entails.eval a c7597 := derived7597 a h
  have h2 : Entails.eval a c1921 := h 1920 (by decide)
  have h3 : Entails.eval a c1897 := h 1896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7599 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7592, some c7598, some c925, some c928, some c907, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7599 : lratChecker f7599 p7599 = .success := by decide +kernel
theorem unsat7599 : Unsatisfiable (PosFin 65) f7599 := by
  apply lratCheckerSound f7599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7599
  · intro a ha; simp [p7599] at ha; subst a; trivial
  · exact checked7599
theorem derived7599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7599 := by
  apply localUnsat_implies_entails f7599 [c7592, c7598, c925, c928, c907] c7599 unsat7599 (by rfl) a
  have h0 : Entails.eval a c7592 := derived7592 a h
  have h1 : Entails.eval a c7598 := derived7598 a h
  have h2 : Entails.eval a c925 := h 924 (by decide)
  have h3 : Entails.eval a c928 := h 927 (by decide)
  have h4 : Entails.eval a c907 := h 906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7600 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7506, some c2594, some c1225, some c2344, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7600 : lratChecker f7600 p7600 = .success := by decide +kernel
theorem unsat7600 : Unsatisfiable (PosFin 65) f7600 := by
  apply lratCheckerSound f7600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7600
  · intro a ha; simp [p7600] at ha; subst a; trivial
  · exact checked7600
theorem derived7600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7600 := by
  apply localUnsat_implies_entails f7600 [c7506, c2594, c1225, c2344] c7600 unsat7600 (by rfl) a
  have h0 : Entails.eval a c7506 := derived7506 a h
  have h1 : Entails.eval a c2594 := h 2593 (by decide)
  have h2 : Entails.eval a c1225 := h 1224 (by decide)
  have h3 : Entails.eval a c2344 := h 2343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7601 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2104, some c2102, some c2114, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p7601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7601 : lratChecker f7601 p7601 = .success := by decide +kernel
theorem unsat7601 : Unsatisfiable (PosFin 65) f7601 := by
  apply lratCheckerSound f7601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7601
  · intro a ha; simp [p7601] at ha; subst a; trivial
  · exact checked7601
theorem derived7601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7601 := by
  apply localUnsat_implies_entails f7601 [c2104, c2102, c2114] c7601 unsat7601 (by rfl) a
  have h0 : Entails.eval a c2104 := h 2103 (by decide)
  have h1 : Entails.eval a c2102 := h 2101 (by decide)
  have h2 : Entails.eval a c2114 := h 2113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7602 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7550, some c7569, some c7571, some c7580, some c7592, some c7595, some c7599, some c7594, some c7130, some c7596, some c1348, some c1362, some c1360, some c7502, some c1355, some c1439, some c1446, some c7600, some c7601, some c7512, some c2344, some c1155, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked7602 : lratChecker f7602 p7602 = .success := by decide +kernel
theorem unsat7602 : Unsatisfiable (PosFin 65) f7602 := by
  apply lratCheckerSound f7602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7602
  · intro a ha; simp [p7602] at ha; subst a; trivial
  · exact checked7602
theorem derived7602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7602 := by
  apply localUnsat_implies_entails f7602 [c7470, c7550, c7569, c7571, c7580, c7592, c7595, c7599, c7594, c7130, c7596, c1348, c1362, c1360, c7502, c1355, c1439, c1446, c7600, c7601, c7512, c2344, c1155] c7602 unsat7602 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7550 := derived7550 a h
  have h2 : Entails.eval a c7569 := derived7569 a h
  have h3 : Entails.eval a c7571 := derived7571 a h
  have h4 : Entails.eval a c7580 := derived7580 a h
  have h5 : Entails.eval a c7592 := derived7592 a h
  have h6 : Entails.eval a c7595 := derived7595 a h
  have h7 : Entails.eval a c7599 := derived7599 a h
  have h8 : Entails.eval a c7594 := derived7594 a h
  have h9 : Entails.eval a c7130 := derived7130 a h
  have h10 : Entails.eval a c7596 := derived7596 a h
  have h11 : Entails.eval a c1348 := h 1347 (by decide)
  have h12 : Entails.eval a c1362 := h 1361 (by decide)
  have h13 : Entails.eval a c1360 := h 1359 (by decide)
  have h14 : Entails.eval a c7502 := derived7502 a h
  have h15 : Entails.eval a c1355 := h 1354 (by decide)
  have h16 : Entails.eval a c1439 := h 1438 (by decide)
  have h17 : Entails.eval a c1446 := h 1445 (by decide)
  have h18 : Entails.eval a c7600 := derived7600 a h
  have h19 : Entails.eval a c7601 := derived7601 a h
  have h20 : Entails.eval a c7512 := derived7512 a h
  have h21 : Entails.eval a c2344 := h 2343 (by decide)
  have h22 : Entails.eval a c1155 := h 1154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7603 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7534, some c7526, some c7525, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7603 : lratChecker f7603 p7603 = .success := by decide +kernel
theorem unsat7603 : Unsatisfiable (PosFin 65) f7603 := by
  apply lratCheckerSound f7603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7603
  · intro a ha; simp [p7603] at ha; subst a; trivial
  · exact checked7603
theorem derived7603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7603 := by
  apply localUnsat_implies_entails f7603 [c7534, c7526, c7525] c7603 unsat7603 (by rfl) a
  have h0 : Entails.eval a c7534 := derived7534 a h
  have h1 : Entails.eval a c7526 := derived7526 a h
  have h2 : Entails.eval a c7525 := derived7525 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7604 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1782, some c1566, some c1732, some c2018, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p7604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7604 : lratChecker f7604 p7604 = .success := by decide +kernel
theorem unsat7604 : Unsatisfiable (PosFin 65) f7604 := by
  apply lratCheckerSound f7604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7604
  · intro a ha; simp [p7604] at ha; subst a; trivial
  · exact checked7604
theorem derived7604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7604 := by
  apply localUnsat_implies_entails f7604 [c1782, c1566, c1732, c2018] c7604 unsat7604 (by rfl) a
  have h0 : Entails.eval a c1782 := h 1781 (by decide)
  have h1 : Entails.eval a c1566 := h 1565 (by decide)
  have h2 : Entails.eval a c1732 := h 1731 (by decide)
  have h3 : Entails.eval a c2018 := h 2017 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7605 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7534, some c7603, some c7531, some c7604, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7605 : lratChecker f7605 p7605 = .success := by decide +kernel
theorem unsat7605 : Unsatisfiable (PosFin 65) f7605 := by
  apply lratCheckerSound f7605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7605
  · intro a ha; simp [p7605] at ha; subst a; trivial
  · exact checked7605
theorem derived7605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7605 := by
  apply localUnsat_implies_entails f7605 [c7534, c7603, c7531, c7604] c7605 unsat7605 (by rfl) a
  have h0 : Entails.eval a c7534 := derived7534 a h
  have h1 : Entails.eval a c7603 := derived7603 a h
  have h2 : Entails.eval a c7531 := derived7531 a h
  have h3 : Entails.eval a c7604 := derived7604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7606 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7534, some c7605, some c7439, some c297, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7606 : lratChecker f7606 p7606 = .success := by decide +kernel
theorem unsat7606 : Unsatisfiable (PosFin 65) f7606 := by
  apply lratCheckerSound f7606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7606
  · intro a ha; simp [p7606] at ha; subst a; trivial
  · exact checked7606
theorem derived7606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7606 := by
  apply localUnsat_implies_entails f7606 [c7534, c7605, c7439, c297] c7606 unsat7606 (by rfl) a
  have h0 : Entails.eval a c7534 := derived7534 a h
  have h1 : Entails.eval a c7605 := derived7605 a h
  have h2 : Entails.eval a c7439 := derived7439 a h
  have h3 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7607 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7526, some c7583, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7607 : lratChecker f7607 p7607 = .success := by decide +kernel
theorem unsat7607 : Unsatisfiable (PosFin 65) f7607 := by
  apply lratCheckerSound f7607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7607
  · intro a ha; simp [p7607] at ha; subst a; trivial
  · exact checked7607
theorem derived7607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7607 := by
  apply localUnsat_implies_entails f7607 [c7526, c7583] c7607 unsat7607 (by rfl) a
  have h0 : Entails.eval a c7526 := derived7526 a h
  have h1 : Entails.eval a c7583 := derived7583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7608 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1341, some c1275, some c7604, some c1889, some c1981, some c1323, some c2670, some c1816, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7608 : lratChecker f7608 p7608 = .success := by decide +kernel
theorem unsat7608 : Unsatisfiable (PosFin 65) f7608 := by
  apply lratCheckerSound f7608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7608
  · intro a ha; simp [p7608] at ha; subst a; trivial
  · exact checked7608
theorem derived7608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7608 := by
  apply localUnsat_implies_entails f7608 [c1341, c1275, c7604, c1889, c1981, c1323, c2670, c1816] c7608 unsat7608 (by rfl) a
  have h0 : Entails.eval a c1341 := h 1340 (by decide)
  have h1 : Entails.eval a c1275 := h 1274 (by decide)
  have h2 : Entails.eval a c7604 := derived7604 a h
  have h3 : Entails.eval a c1889 := h 1888 (by decide)
  have h4 : Entails.eval a c1981 := h 1980 (by decide)
  have h5 : Entails.eval a c1323 := h 1322 (by decide)
  have h6 : Entails.eval a c2670 := h 2669 (by decide)
  have h7 : Entails.eval a c1816 := h 1815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7609 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7608, some c7526, some c7607, some c1287, some c1352, some c151, some c2026, some c2111, some c1900, some c127, some c3117, some c933, some c1061, some c1079, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7609 : lratChecker f7609 p7609 = .success := by decide +kernel
theorem unsat7609 : Unsatisfiable (PosFin 65) f7609 := by
  apply lratCheckerSound f7609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7609
  · intro a ha; simp [p7609] at ha; subst a; trivial
  · exact checked7609
theorem derived7609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7609 := by
  apply localUnsat_implies_entails f7609 [c7608, c7526, c7607, c1287, c1352, c151, c2026, c2111, c1900, c127, c3117, c933, c1061, c1079] c7609 unsat7609 (by rfl) a
  have h0 : Entails.eval a c7608 := derived7608 a h
  have h1 : Entails.eval a c7526 := derived7526 a h
  have h2 : Entails.eval a c7607 := derived7607 a h
  have h3 : Entails.eval a c1287 := h 1286 (by decide)
  have h4 : Entails.eval a c1352 := h 1351 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c2026 := h 2025 (by decide)
  have h7 : Entails.eval a c2111 := h 2110 (by decide)
  have h8 : Entails.eval a c1900 := h 1899 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c3117 := h 3116 (by decide)
  have h11 : Entails.eval a c933 := h 932 (by decide)
  have h12 : Entails.eval a c1061 := h 1060 (by decide)
  have h13 : Entails.eval a c1079 := h 1078 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7610 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7592, some c925, some c929, some c7508, some c1324, some c2077, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7610 : lratChecker f7610 p7610 = .success := by decide +kernel
theorem unsat7610 : Unsatisfiable (PosFin 65) f7610 := by
  apply lratCheckerSound f7610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7610
  · intro a ha; simp [p7610] at ha; subst a; trivial
  · exact checked7610
theorem derived7610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7610 := by
  apply localUnsat_implies_entails f7610 [c7592, c925, c929, c7508, c1324, c2077] c7610 unsat7610 (by rfl) a
  have h0 : Entails.eval a c7592 := derived7592 a h
  have h1 : Entails.eval a c925 := h 924 (by decide)
  have h2 : Entails.eval a c929 := h 928 (by decide)
  have h3 : Entails.eval a c7508 := derived7508 a h
  have h4 : Entails.eval a c1324 := h 1323 (by decide)
  have h5 : Entails.eval a c2077 := h 2076 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7611 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7606, some c7601, some c7542, some c1929, some c1091, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7611 : lratChecker f7611 p7611 = .success := by decide +kernel
theorem unsat7611 : Unsatisfiable (PosFin 65) f7611 := by
  apply lratCheckerSound f7611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7611
  · intro a ha; simp [p7611] at ha; subst a; trivial
  · exact checked7611
theorem derived7611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7611 := by
  apply localUnsat_implies_entails f7611 [c7606, c7601, c7542, c1929, c1091] c7611 unsat7611 (by rfl) a
  have h0 : Entails.eval a c7606 := derived7606 a h
  have h1 : Entails.eval a c7601 := derived7601 a h
  have h2 : Entails.eval a c7542 := derived7542 a h
  have h3 : Entails.eval a c1929 := h 1928 (by decide)
  have h4 : Entails.eval a c1091 := h 1090 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7612 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7606, some c7592, some c7610, some c7130, some c7596, some c1362, some c1359, some c1340, some c7537, some c1355, some c7611, some c1439, some c740, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7612 : lratChecker f7612 p7612 = .success := by decide +kernel
theorem unsat7612 : Unsatisfiable (PosFin 65) f7612 := by
  apply lratCheckerSound f7612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7612
  · intro a ha; simp [p7612] at ha; subst a; trivial
  · exact checked7612
theorem derived7612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7612 := by
  apply localUnsat_implies_entails f7612 [c7569, c7606, c7592, c7610, c7130, c7596, c1362, c1359, c1340, c7537, c1355, c7611, c1439, c740] c7612 unsat7612 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7606 := derived7606 a h
  have h2 : Entails.eval a c7592 := derived7592 a h
  have h3 : Entails.eval a c7610 := derived7610 a h
  have h4 : Entails.eval a c7130 := derived7130 a h
  have h5 : Entails.eval a c7596 := derived7596 a h
  have h6 : Entails.eval a c1362 := h 1361 (by decide)
  have h7 : Entails.eval a c1359 := h 1358 (by decide)
  have h8 : Entails.eval a c1340 := h 1339 (by decide)
  have h9 : Entails.eval a c7537 := derived7537 a h
  have h10 : Entails.eval a c1355 := h 1354 (by decide)
  have h11 : Entails.eval a c7611 := derived7611 a h
  have h12 : Entails.eval a c1439 := h 1438 (by decide)
  have h13 : Entails.eval a c740 := h 739 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7613 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7550, some c7569, some c7602, some c7606, some c7609, some c7612, some c7599, some c7607, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7613 : lratChecker f7613 p7613 = .success := by decide +kernel
theorem unsat7613 : Unsatisfiable (PosFin 65) f7613 := by
  apply lratCheckerSound f7613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7613
  · intro a ha; simp [p7613] at ha; subst a; trivial
  · exact checked7613
theorem derived7613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7613 := by
  apply localUnsat_implies_entails f7613 [c7470, c7550, c7569, c7602, c7606, c7609, c7612, c7599, c7607] c7613 unsat7613 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7550 := derived7550 a h
  have h2 : Entails.eval a c7569 := derived7569 a h
  have h3 : Entails.eval a c7602 := derived7602 a h
  have h4 : Entails.eval a c7606 := derived7606 a h
  have h5 : Entails.eval a c7609 := derived7609 a h
  have h6 : Entails.eval a c7612 := derived7612 a h
  have h7 : Entails.eval a c7599 := derived7599 a h
  have h8 : Entails.eval a c7607 := derived7607 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7614 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c899, some c906, some c1440, some c715, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7614 : lratChecker f7614 p7614 = .success := by decide +kernel
theorem unsat7614 : Unsatisfiable (PosFin 65) f7614 := by
  apply lratCheckerSound f7614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7614
  · intro a ha; simp [p7614] at ha; subst a; trivial
  · exact checked7614
theorem derived7614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7614 := by
  apply localUnsat_implies_entails f7614 [c899, c906, c1440, c715] c7614 unsat7614 (by rfl) a
  have h0 : Entails.eval a c899 := h 898 (by decide)
  have h1 : Entails.eval a c906 := h 905 (by decide)
  have h2 : Entails.eval a c1440 := h 1439 (by decide)
  have h3 : Entails.eval a c715 := h 714 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7615 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7573, some c7576, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7615 : lratChecker f7615 p7615 = .success := by decide +kernel
theorem unsat7615 : Unsatisfiable (PosFin 65) f7615 := by
  apply lratCheckerSound f7615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7615
  · intro a ha; simp [p7615] at ha; subst a; trivial
  · exact checked7615
theorem derived7615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7615 := by
  apply localUnsat_implies_entails f7615 [c7573, c7576] c7615 unsat7615 (by rfl) a
  have h0 : Entails.eval a c7573 := derived7573 a h
  have h1 : Entails.eval a c7576 := derived7576 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7616 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7581, some c7614, some c7586, some c7615, some c1440, some c715, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7616 : lratChecker f7616 p7616 = .success := by decide +kernel
theorem unsat7616 : Unsatisfiable (PosFin 65) f7616 := by
  apply lratCheckerSound f7616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7616
  · intro a ha; simp [p7616] at ha; subst a; trivial
  · exact checked7616
theorem derived7616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7616 := by
  apply localUnsat_implies_entails f7616 [c7581, c7614, c7586, c7615, c1440, c715] c7616 unsat7616 (by rfl) a
  have h0 : Entails.eval a c7581 := derived7581 a h
  have h1 : Entails.eval a c7614 := derived7614 a h
  have h2 : Entails.eval a c7586 := derived7586 a h
  have h3 : Entails.eval a c7615 := derived7615 a h
  have h4 : Entails.eval a c1440 := h 1439 (by decide)
  have h5 : Entails.eval a c715 := h 714 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7617 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1286, some c1289, some c1294, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7617 : lratChecker f7617 p7617 = .success := by decide +kernel
theorem unsat7617 : Unsatisfiable (PosFin 65) f7617 := by
  apply lratCheckerSound f7617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7617
  · intro a ha; simp [p7617] at ha; subst a; trivial
  · exact checked7617
theorem derived7617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7617 := by
  apply localUnsat_implies_entails f7617 [c1286, c1289, c1294] c7617 unsat7617 (by rfl) a
  have h0 : Entails.eval a c1286 := h 1285 (by decide)
  have h1 : Entails.eval a c1289 := h 1288 (by decide)
  have h2 : Entails.eval a c1294 := h 1293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7618 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c903, some c902, some c931, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7618 : lratChecker f7618 p7618 = .success := by decide +kernel
theorem unsat7618 : Unsatisfiable (PosFin 65) f7618 := by
  apply lratCheckerSound f7618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7618
  · intro a ha; simp [p7618] at ha; subst a; trivial
  · exact checked7618
theorem derived7618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7618 := by
  apply localUnsat_implies_entails f7618 [c903, c902, c931] c7618 unsat7618 (by rfl) a
  have h0 : Entails.eval a c903 := h 902 (by decide)
  have h1 : Entails.eval a c902 := h 901 (by decide)
  have h2 : Entails.eval a c931 := h 930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7619 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c699, some c1425, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7619 : lratChecker f7619 p7619 = .success := by decide +kernel
theorem unsat7619 : Unsatisfiable (PosFin 65) f7619 := by
  apply lratCheckerSound f7619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7619
  · intro a ha; simp [p7619] at ha; subst a; trivial
  · exact checked7619
theorem derived7619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7619 := by
  apply localUnsat_implies_entails f7619 [c699, c1425] c7619 unsat7619 (by rfl) a
  have h0 : Entails.eval a c699 := h 698 (by decide)
  have h1 : Entails.eval a c1425 := h 1424 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7620 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1428, some c1441, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7620 : lratChecker f7620 p7620 = .success := by decide +kernel
theorem unsat7620 : Unsatisfiable (PosFin 65) f7620 := by
  apply lratCheckerSound f7620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7620
  · intro a ha; simp [p7620] at ha; subst a; trivial
  · exact checked7620
theorem derived7620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7620 := by
  apply localUnsat_implies_entails f7620 [c1428, c1441] c7620 unsat7620 (by rfl) a
  have h0 : Entails.eval a c1428 := h 1427 (by decide)
  have h1 : Entails.eval a c1441 := h 1440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7621 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7294, some c7619, some c7620, some c702, some c717, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7621 : lratChecker f7621 p7621 = .success := by decide +kernel
theorem unsat7621 : Unsatisfiable (PosFin 65) f7621 := by
  apply lratCheckerSound f7621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7621
  · intro a ha; simp [p7621] at ha; subst a; trivial
  · exact checked7621
theorem derived7621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7621 := by
  apply localUnsat_implies_entails f7621 [c7294, c7619, c7620, c702, c717] c7621 unsat7621 (by rfl) a
  have h0 : Entails.eval a c7294 := derived7294 a h
  have h1 : Entails.eval a c7619 := derived7619 a h
  have h2 : Entails.eval a c7620 := derived7620 a h
  have h3 : Entails.eval a c702 := h 701 (by decide)
  have h4 : Entails.eval a c717 := h 716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7622 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7526, some c7573, some c7582, some c1060, some c1061, some c1074, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7622 : lratChecker f7622 p7622 = .success := by decide +kernel
theorem unsat7622 : Unsatisfiable (PosFin 65) f7622 := by
  apply lratCheckerSound f7622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7622
  · intro a ha; simp [p7622] at ha; subst a; trivial
  · exact checked7622
theorem derived7622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7622 := by
  apply localUnsat_implies_entails f7622 [c7526, c7573, c7582, c1060, c1061, c1074] c7622 unsat7622 (by rfl) a
  have h0 : Entails.eval a c7526 := derived7526 a h
  have h1 : Entails.eval a c7573 := derived7573 a h
  have h2 : Entails.eval a c7582 := derived7582 a h
  have h3 : Entails.eval a c1060 := h 1059 (by decide)
  have h4 : Entails.eval a c1061 := h 1060 (by decide)
  have h5 : Entails.eval a c1074 := h 1073 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7623 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1351, some c1899, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7623 : lratChecker f7623 p7623 = .success := by decide +kernel
theorem unsat7623 : Unsatisfiable (PosFin 65) f7623 := by
  apply lratCheckerSound f7623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7623
  · intro a ha; simp [p7623] at ha; subst a; trivial
  · exact checked7623
theorem derived7623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7623 := by
  apply localUnsat_implies_entails f7623 [c1351, c1899] c7623 unsat7623 (by rfl) a
  have h0 : Entails.eval a c1351 := h 1350 (by decide)
  have h1 : Entails.eval a c1899 := h 1898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7624 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c731, some c741, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7624 : lratChecker f7624 p7624 = .success := by decide +kernel
theorem unsat7624 : Unsatisfiable (PosFin 65) f7624 := by
  apply lratCheckerSound f7624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7624
  · intro a ha; simp [p7624] at ha; subst a; trivial
  · exact checked7624
theorem derived7624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7624 := by
  apply localUnsat_implies_entails f7624 [c731, c741] c7624 unsat7624 (by rfl) a
  have h0 : Entails.eval a c731 := h 730 (by decide)
  have h1 : Entails.eval a c741 := h 740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7625 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7621, some c7545, some c7617, some c7620, some c7624, some c1130, some c1135, some c1349, some c1969, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7625 : lratChecker f7625 p7625 = .success := by decide +kernel
theorem unsat7625 : Unsatisfiable (PosFin 65) f7625 := by
  apply lratCheckerSound f7625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7625
  · intro a ha; simp [p7625] at ha; subst a; trivial
  · exact checked7625
theorem derived7625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7625 := by
  apply localUnsat_implies_entails f7625 [c7569, c7621, c7545, c7617, c7620, c7624, c1130, c1135, c1349, c1969] c7625 unsat7625 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7621 := derived7621 a h
  have h2 : Entails.eval a c7545 := derived7545 a h
  have h3 : Entails.eval a c7617 := derived7617 a h
  have h4 : Entails.eval a c7620 := derived7620 a h
  have h5 : Entails.eval a c7624 := derived7624 a h
  have h6 : Entails.eval a c1130 := h 1129 (by decide)
  have h7 : Entails.eval a c1135 := h 1134 (by decide)
  have h8 : Entails.eval a c1349 := h 1348 (by decide)
  have h9 : Entails.eval a c1969 := h 1968 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7626 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7550, some c7569, some c7613, some c7621, some c7545, some c7617, some c7625, some c1351, some c1425, some c1967, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7626 : lratChecker f7626 p7626 = .success := by decide +kernel
theorem unsat7626 : Unsatisfiable (PosFin 65) f7626 := by
  apply lratCheckerSound f7626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7626
  · intro a ha; simp [p7626] at ha; subst a; trivial
  · exact checked7626
theorem derived7626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7626 := by
  apply localUnsat_implies_entails f7626 [c7470, c7550, c7569, c7613, c7621, c7545, c7617, c7625, c1351, c1425, c1967] c7626 unsat7626 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7550 := derived7550 a h
  have h2 : Entails.eval a c7569 := derived7569 a h
  have h3 : Entails.eval a c7613 := derived7613 a h
  have h4 : Entails.eval a c7621 := derived7621 a h
  have h5 : Entails.eval a c7545 := derived7545 a h
  have h6 : Entails.eval a c7617 := derived7617 a h
  have h7 : Entails.eval a c7625 := derived7625 a h
  have h8 : Entails.eval a c1351 := h 1350 (by decide)
  have h9 : Entails.eval a c1425 := h 1424 (by decide)
  have h10 : Entails.eval a c1967 := h 1966 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7627 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c761, some c777, some c764, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7627 : lratChecker f7627 p7627 = .success := by decide +kernel
theorem unsat7627 : Unsatisfiable (PosFin 65) f7627 := by
  apply lratCheckerSound f7627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7627
  · intro a ha; simp [p7627] at ha; subst a; trivial
  · exact checked7627
theorem derived7627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7627 := by
  apply localUnsat_implies_entails f7627 [c761, c777, c764] c7627 unsat7627 (by rfl) a
  have h0 : Entails.eval a c761 := h 760 (by decide)
  have h1 : Entails.eval a c777 := h 776 (by decide)
  have h2 : Entails.eval a c764 := h 763 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7628 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7627, some c748, some c7218, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7628 : lratChecker f7628 p7628 = .success := by decide +kernel
theorem unsat7628 : Unsatisfiable (PosFin 65) f7628 := by
  apply lratCheckerSound f7628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7628
  · intro a ha; simp [p7628] at ha; subst a; trivial
  · exact checked7628
theorem derived7628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7628 := by
  apply localUnsat_implies_entails f7628 [c7627, c748, c7218] c7628 unsat7628 (by rfl) a
  have h0 : Entails.eval a c7627 := derived7627 a h
  have h1 : Entails.eval a c748 := h 747 (by decide)
  have h2 : Entails.eval a c7218 := derived7218 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7629 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7501, some c778, some c764, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7629 : lratChecker f7629 p7629 = .success := by decide +kernel
theorem unsat7629 : Unsatisfiable (PosFin 65) f7629 := by
  apply lratCheckerSound f7629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7629
  · intro a ha; simp [p7629] at ha; subst a; trivial
  · exact checked7629
theorem derived7629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7629 := by
  apply localUnsat_implies_entails f7629 [c7501, c778, c764] c7629 unsat7629 (by rfl) a
  have h0 : Entails.eval a c7501 := derived7501 a h
  have h1 : Entails.eval a c778 := h 777 (by decide)
  have h2 : Entails.eval a c764 := h 763 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7630 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7628, some c7304, some c7629, some c748, some c339, some c354, some c341, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7630 : lratChecker f7630 p7630 = .success := by decide +kernel
theorem unsat7630 : Unsatisfiable (PosFin 65) f7630 := by
  apply lratCheckerSound f7630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7630
  · intro a ha; simp [p7630] at ha; subst a; trivial
  · exact checked7630
theorem derived7630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7630 := by
  apply localUnsat_implies_entails f7630 [c7628, c7304, c7629, c748, c339, c354, c341] c7630 unsat7630 (by rfl) a
  have h0 : Entails.eval a c7628 := derived7628 a h
  have h1 : Entails.eval a c7304 := derived7304 a h
  have h2 : Entails.eval a c7629 := derived7629 a h
  have h3 : Entails.eval a c748 := h 747 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7631 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7627, some c755, some c748, some c766, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7631 : lratChecker f7631 p7631 = .success := by decide +kernel
theorem unsat7631 : Unsatisfiable (PosFin 65) f7631 := by
  apply lratCheckerSound f7631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7631
  · intro a ha; simp [p7631] at ha; subst a; trivial
  · exact checked7631
theorem derived7631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7631 := by
  apply localUnsat_implies_entails f7631 [c7627, c755, c748, c766] c7631 unsat7631 (by rfl) a
  have h0 : Entails.eval a c7627 := derived7627 a h
  have h1 : Entails.eval a c755 := h 754 (by decide)
  have h2 : Entails.eval a c748 := h 747 (by decide)
  have h3 : Entails.eval a c766 := h 765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7632 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2288, some c906, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7632 : lratChecker f7632 p7632 = .success := by decide +kernel
theorem unsat7632 : Unsatisfiable (PosFin 65) f7632 := by
  apply lratCheckerSound f7632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7632
  · intro a ha; simp [p7632] at ha; subst a; trivial
  · exact checked7632
theorem derived7632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7632 := by
  apply localUnsat_implies_entails f7632 [c2288, c906] c7632 unsat7632 (by rfl) a
  have h0 : Entails.eval a c2288 := h 2287 (by decide)
  have h1 : Entails.eval a c906 := h 905 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7633 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c886, some c892, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7633 : lratChecker f7633 p7633 = .success := by decide +kernel
theorem unsat7633 : Unsatisfiable (PosFin 65) f7633 := by
  apply lratCheckerSound f7633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7633
  · intro a ha; simp [p7633] at ha; subst a; trivial
  · exact checked7633
theorem derived7633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7633 := by
  apply localUnsat_implies_entails f7633 [c886, c892] c7633 unsat7633 (by rfl) a
  have h0 : Entails.eval a c886 := h 885 (by decide)
  have h1 : Entails.eval a c892 := h 891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7634 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1011, some c931, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7634 : lratChecker f7634 p7634 = .success := by decide +kernel
theorem unsat7634 : Unsatisfiable (PosFin 65) f7634 := by
  apply lratCheckerSound f7634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7634
  · intro a ha; simp [p7634] at ha; subst a; trivial
  · exact checked7634
theorem derived7634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7634 := by
  apply localUnsat_implies_entails f7634 [c1011, c931] c7634 unsat7634 (by rfl) a
  have h0 : Entails.eval a c1011 := h 1010 (by decide)
  have h1 : Entails.eval a c931 := h 930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7635 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7631, some c7630, some c7501, some c7629, some c764, some c759, some c780, some c770, some c753, some c7528, some c768, some c775, some c7632, some c7634, some c7522, some c7512, some c713, some c1459, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7635 : lratChecker f7635 p7635 = .success := by decide +kernel
theorem unsat7635 : Unsatisfiable (PosFin 65) f7635 := by
  apply lratCheckerSound f7635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7635
  · intro a ha; simp [p7635] at ha; subst a; trivial
  · exact checked7635
theorem derived7635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7635 := by
  apply localUnsat_implies_entails f7635 [c7631, c7630, c7501, c7629, c764, c759, c780, c770, c753, c7528, c768, c775, c7632, c7634, c7522, c7512, c713, c1459] c7635 unsat7635 (by rfl) a
  have h0 : Entails.eval a c7631 := derived7631 a h
  have h1 : Entails.eval a c7630 := derived7630 a h
  have h2 : Entails.eval a c7501 := derived7501 a h
  have h3 : Entails.eval a c7629 := derived7629 a h
  have h4 : Entails.eval a c764 := h 763 (by decide)
  have h5 : Entails.eval a c759 := h 758 (by decide)
  have h6 : Entails.eval a c780 := h 779 (by decide)
  have h7 : Entails.eval a c770 := h 769 (by decide)
  have h8 : Entails.eval a c753 := h 752 (by decide)
  have h9 : Entails.eval a c7528 := derived7528 a h
  have h10 : Entails.eval a c768 := h 767 (by decide)
  have h11 : Entails.eval a c775 := h 774 (by decide)
  have h12 : Entails.eval a c7632 := derived7632 a h
  have h13 : Entails.eval a c7634 := derived7634 a h
  have h14 : Entails.eval a c7522 := derived7522 a h
  have h15 : Entails.eval a c7512 := derived7512 a h
  have h16 : Entails.eval a c713 := h 712 (by decide)
  have h17 : Entails.eval a c1459 := h 1458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7636 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2283, some c898, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7636 : lratChecker f7636 p7636 = .success := by decide +kernel
theorem unsat7636 : Unsatisfiable (PosFin 65) f7636 := by
  apply lratCheckerSound f7636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7636
  · intro a ha; simp [p7636] at ha; subst a; trivial
  · exact checked7636
theorem derived7636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7636 := by
  apply localUnsat_implies_entails f7636 [c2283, c898] c7636 unsat7636 (by rfl) a
  have h0 : Entails.eval a c2283 := h 2282 (by decide)
  have h1 : Entails.eval a c898 := h 897 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7637 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c911, some c927, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7637 : lratChecker f7637 p7637 = .success := by decide +kernel
theorem unsat7637 : Unsatisfiable (PosFin 65) f7637 := by
  apply lratCheckerSound f7637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7637
  · intro a ha; simp [p7637] at ha; subst a; trivial
  · exact checked7637
theorem derived7637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7637 := by
  apply localUnsat_implies_entails f7637 [c911, c927] c7637 unsat7637 (by rfl) a
  have h0 : Entails.eval a c911 := h 910 (by decide)
  have h1 : Entails.eval a c927 := h 926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7638 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨21, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c764, some c784, some c760, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7638 : lratChecker f7638 p7638 = .success := by decide +kernel
theorem unsat7638 : Unsatisfiable (PosFin 65) f7638 := by
  apply lratCheckerSound f7638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7638
  · intro a ha; simp [p7638] at ha; subst a; trivial
  · exact checked7638
theorem derived7638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7638 := by
  apply localUnsat_implies_entails f7638 [c764, c784, c760] c7638 unsat7638 (by rfl) a
  have h0 : Entails.eval a c764 := h 763 (by decide)
  have h1 : Entails.eval a c784 := h 783 (by decide)
  have h2 : Entails.eval a c760 := h 759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7639 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c878, some c874, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7639 : lratChecker f7639 p7639 = .success := by decide +kernel
theorem unsat7639 : Unsatisfiable (PosFin 65) f7639 := by
  apply lratCheckerSound f7639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7639
  · intro a ha; simp [p7639] at ha; subst a; trivial
  · exact checked7639
theorem derived7639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7639 := by
  apply localUnsat_implies_entails f7639 [c878, c874] c7639 unsat7639 (by rfl) a
  have h0 : Entails.eval a c878 := h 877 (by decide)
  have h1 : Entails.eval a c874 := h 873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7640 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c814, some c801, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7640 : lratChecker f7640 p7640 = .success := by decide +kernel
theorem unsat7640 : Unsatisfiable (PosFin 65) f7640 := by
  apply lratCheckerSound f7640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7640
  · intro a ha; simp [p7640] at ha; subst a; trivial
  · exact checked7640
theorem derived7640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7640 := by
  apply localUnsat_implies_entails f7640 [c814, c801] c7640 unsat7640 (by rfl) a
  have h0 : Entails.eval a c814 := h 813 (by decide)
  have h1 : Entails.eval a c801 := h 800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7641 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7630, some c7631, some c7635, some c755, some c748, some c773, some c768, some c775, some c7636, some c7637, some c7638, some c779, some c780, some c2299, some c7522, some c7640, some c7512, some c713, some c1459, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7641 : lratChecker f7641 p7641 = .success := by decide +kernel
theorem unsat7641 : Unsatisfiable (PosFin 65) f7641 := by
  apply lratCheckerSound f7641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7641
  · intro a ha; simp [p7641] at ha; subst a; trivial
  · exact checked7641
theorem derived7641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7641 := by
  apply localUnsat_implies_entails f7641 [c7630, c7631, c7635, c755, c748, c773, c768, c775, c7636, c7637, c7638, c779, c780, c2299, c7522, c7640, c7512, c713, c1459] c7641 unsat7641 (by rfl) a
  have h0 : Entails.eval a c7630 := derived7630 a h
  have h1 : Entails.eval a c7631 := derived7631 a h
  have h2 : Entails.eval a c7635 := derived7635 a h
  have h3 : Entails.eval a c755 := h 754 (by decide)
  have h4 : Entails.eval a c748 := h 747 (by decide)
  have h5 : Entails.eval a c773 := h 772 (by decide)
  have h6 : Entails.eval a c768 := h 767 (by decide)
  have h7 : Entails.eval a c775 := h 774 (by decide)
  have h8 : Entails.eval a c7636 := derived7636 a h
  have h9 : Entails.eval a c7637 := derived7637 a h
  have h10 : Entails.eval a c7638 := derived7638 a h
  have h11 : Entails.eval a c779 := h 778 (by decide)
  have h12 : Entails.eval a c780 := h 779 (by decide)
  have h13 : Entails.eval a c2299 := h 2298 (by decide)
  have h14 : Entails.eval a c7522 := derived7522 a h
  have h15 : Entails.eval a c7640 := derived7640 a h
  have h16 : Entails.eval a c7512 := derived7512 a h
  have h17 : Entails.eval a c713 := h 712 (by decide)
  have h18 : Entails.eval a c1459 := h 1458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7642 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1110, some c7525, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7642 : lratChecker f7642 p7642 = .success := by decide +kernel
theorem unsat7642 : Unsatisfiable (PosFin 65) f7642 := by
  apply lratCheckerSound f7642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7642
  · intro a ha; simp [p7642] at ha; subst a; trivial
  · exact checked7642
theorem derived7642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7642 := by
  apply localUnsat_implies_entails f7642 [c1110, c7525] c7642 unsat7642 (by rfl) a
  have h0 : Entails.eval a c1110 := h 1109 (by decide)
  have h1 : Entails.eval a c7525 := derived7525 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7643 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7642, some c7563, some c7531, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7643 : lratChecker f7643 p7643 = .success := by decide +kernel
theorem unsat7643 : Unsatisfiable (PosFin 65) f7643 := by
  apply lratCheckerSound f7643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7643
  · intro a ha; simp [p7643] at ha; subst a; trivial
  · exact checked7643
theorem derived7643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7643 := by
  apply localUnsat_implies_entails f7643 [c7642, c7563, c7531] c7643 unsat7643 (by rfl) a
  have h0 : Entails.eval a c7642 := derived7642 a h
  have h1 : Entails.eval a c7563 := derived7563 a h
  have h2 : Entails.eval a c7531 := derived7531 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7644 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1055, some c1110, some c1382, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7644 : lratChecker f7644 p7644 = .success := by decide +kernel
theorem unsat7644 : Unsatisfiable (PosFin 65) f7644 := by
  apply lratCheckerSound f7644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7644
  · intro a ha; simp [p7644] at ha; subst a; trivial
  · exact checked7644
theorem derived7644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7644 := by
  apply localUnsat_implies_entails f7644 [c1055, c1110, c1382] c7644 unsat7644 (by rfl) a
  have h0 : Entails.eval a c1055 := h 1054 (by decide)
  have h1 : Entails.eval a c1110 := h 1109 (by decide)
  have h2 : Entails.eval a c1382 := h 1381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7645 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c797, some c802, some c796, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7645 : lratChecker f7645 p7645 = .success := by decide +kernel
theorem unsat7645 : Unsatisfiable (PosFin 65) f7645 := by
  apply lratCheckerSound f7645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7645
  · intro a ha; simp [p7645] at ha; subst a; trivial
  · exact checked7645
theorem derived7645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7645 := by
  apply localUnsat_implies_entails f7645 [c797, c802, c796] c7645 unsat7645 (by rfl) a
  have h0 : Entails.eval a c797 := h 796 (by decide)
  have h1 : Entails.eval a c802 := h 801 (by decide)
  have h2 : Entails.eval a c796 := h 795 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7646 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7645, some c1117, some c1122, some c1116, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7646 : lratChecker f7646 p7646 = .success := by decide +kernel
theorem unsat7646 : Unsatisfiable (PosFin 65) f7646 := by
  apply lratCheckerSound f7646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7646
  · intro a ha; simp [p7646] at ha; subst a; trivial
  · exact checked7646
theorem derived7646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7646 := by
  apply localUnsat_implies_entails f7646 [c7645, c1117, c1122, c1116] c7646 unsat7646 (by rfl) a
  have h0 : Entails.eval a c7645 := derived7645 a h
  have h1 : Entails.eval a c1117 := h 1116 (by decide)
  have h2 : Entails.eval a c1122 := h 1121 (by decide)
  have h3 : Entails.eval a c1116 := h 1115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7647 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7490, some c1055, some c1110, some c2537, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7647 : lratChecker f7647 p7647 = .success := by decide +kernel
theorem unsat7647 : Unsatisfiable (PosFin 65) f7647 := by
  apply lratCheckerSound f7647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7647
  · intro a ha; simp [p7647] at ha; subst a; trivial
  · exact checked7647
theorem derived7647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7647 := by
  apply localUnsat_implies_entails f7647 [c7490, c1055, c1110, c2537] c7647 unsat7647 (by rfl) a
  have h0 : Entails.eval a c7490 := derived7490 a h
  have h1 : Entails.eval a c1055 := h 1054 (by decide)
  have h2 : Entails.eval a c1110 := h 1109 (by decide)
  have h3 : Entails.eval a c2537 := h 2536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7648 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7646, some c7643, some c7647, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7648 : lratChecker f7648 p7648 = .success := by decide +kernel
theorem unsat7648 : Unsatisfiable (PosFin 65) f7648 := by
  apply lratCheckerSound f7648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7648
  · intro a ha; simp [p7648] at ha; subst a; trivial
  · exact checked7648
theorem derived7648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7648 := by
  apply localUnsat_implies_entails f7648 [c7641, c7646, c7643, c7647] c7648 unsat7648 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7646 := derived7646 a h
  have h2 : Entails.eval a c7643 := derived7643 a h
  have h3 : Entails.eval a c7647 := derived7647 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7649 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7439, some c297, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7649 : lratChecker f7649 p7649 = .success := by decide +kernel
theorem unsat7649 : Unsatisfiable (PosFin 65) f7649 := by
  apply lratCheckerSound f7649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7649
  · intro a ha; simp [p7649] at ha; subst a; trivial
  · exact checked7649
theorem derived7649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7649 := by
  apply localUnsat_implies_entails f7649 [c7439, c297] c7649 unsat7649 (by rfl) a
  have h0 : Entails.eval a c7439 := derived7439 a h
  have h1 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7650 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7649, some c7251, some c1122, some c1127, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7650 : lratChecker f7650 p7650 = .success := by decide +kernel
theorem unsat7650 : Unsatisfiable (PosFin 65) f7650 := by
  apply lratCheckerSound f7650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7650
  · intro a ha; simp [p7650] at ha; subst a; trivial
  · exact checked7650
theorem derived7650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7650 := by
  apply localUnsat_implies_entails f7650 [c7649, c7251, c1122, c1127] c7650 unsat7650 (by rfl) a
  have h0 : Entails.eval a c7649 := derived7649 a h
  have h1 : Entails.eval a c7251 := derived7251 a h
  have h2 : Entails.eval a c1122 := h 1121 (by decide)
  have h3 : Entails.eval a c1127 := h 1126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7651 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7648, some c7650, some c793, some c1127, some c1142, some c1131, some c1121, some c1109, some c2617, some c7485, some c2544, some c1067, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7651 : lratChecker f7651 p7651 = .success := by decide +kernel
theorem unsat7651 : Unsatisfiable (PosFin 65) f7651 := by
  apply lratCheckerSound f7651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7651
  · intro a ha; simp [p7651] at ha; subst a; trivial
  · exact checked7651
theorem derived7651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7651 := by
  apply localUnsat_implies_entails f7651 [c7641, c7648, c7650, c793, c1127, c1142, c1131, c1121, c1109, c2617, c7485, c2544, c1067] c7651 unsat7651 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7648 := derived7648 a h
  have h2 : Entails.eval a c7650 := derived7650 a h
  have h3 : Entails.eval a c793 := h 792 (by decide)
  have h4 : Entails.eval a c1127 := h 1126 (by decide)
  have h5 : Entails.eval a c1142 := h 1141 (by decide)
  have h6 : Entails.eval a c1131 := h 1130 (by decide)
  have h7 : Entails.eval a c1121 := h 1120 (by decide)
  have h8 : Entails.eval a c1109 := h 1108 (by decide)
  have h9 : Entails.eval a c2617 := h 2616 (by decide)
  have h10 : Entails.eval a c7485 := derived7485 a h
  have h11 : Entails.eval a c2544 := h 2543 (by decide)
  have h12 : Entails.eval a c1067 := h 1066 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7652 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c787, some c802, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7652 : lratChecker f7652 p7652 = .success := by decide +kernel
theorem unsat7652 : Unsatisfiable (PosFin 65) f7652 := by
  apply lratCheckerSound f7652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7652
  · intro a ha; simp [p7652] at ha; subst a; trivial
  · exact checked7652
theorem derived7652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7652 := by
  apply localUnsat_implies_entails f7652 [c787, c802] c7652 unsat7652 (by rfl) a
  have h0 : Entails.eval a c787 := h 786 (by decide)
  have h1 : Entails.eval a c802 := h 801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7653 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7648, some c7651, some c7652, some c1122, some c1127, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7653 : lratChecker f7653 p7653 = .success := by decide +kernel
theorem unsat7653 : Unsatisfiable (PosFin 65) f7653 := by
  apply lratCheckerSound f7653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7653
  · intro a ha; simp [p7653] at ha; subst a; trivial
  · exact checked7653
theorem derived7653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7653 := by
  apply localUnsat_implies_entails f7653 [c7641, c7648, c7651, c7652, c1122, c1127] c7653 unsat7653 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7648 := derived7648 a h
  have h2 : Entails.eval a c7651 := derived7651 a h
  have h3 : Entails.eval a c7652 := derived7652 a h
  have h4 : Entails.eval a c1122 := h 1121 (by decide)
  have h5 : Entails.eval a c1127 := h 1126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7654 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7525, some c1114, some c1112, some c1791, some c295, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7654 : lratChecker f7654 p7654 = .success := by decide +kernel
theorem unsat7654 : Unsatisfiable (PosFin 65) f7654 := by
  apply lratCheckerSound f7654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7654
  · intro a ha; simp [p7654] at ha; subst a; trivial
  · exact checked7654
theorem derived7654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7654 := by
  apply localUnsat_implies_entails f7654 [c7525, c1114, c1112, c1791, c295] c7654 unsat7654 (by rfl) a
  have h0 : Entails.eval a c7525 := derived7525 a h
  have h1 : Entails.eval a c1114 := h 1113 (by decide)
  have h2 : Entails.eval a c1112 := h 1111 (by decide)
  have h3 : Entails.eval a c1791 := h 1790 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7655 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7533, some c7654, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7655 : lratChecker f7655 p7655 = .success := by decide +kernel
theorem unsat7655 : Unsatisfiable (PosFin 65) f7655 := by
  apply lratCheckerSound f7655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7655
  · intro a ha; simp [p7655] at ha; subst a; trivial
  · exact checked7655
theorem derived7655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7655 := by
  apply localUnsat_implies_entails f7655 [c7533, c7654] c7655 unsat7655 (by rfl) a
  have h0 : Entails.eval a c7533 := derived7533 a h
  have h1 : Entails.eval a c7654 := derived7654 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7656 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7528, some c798, some c799, some c796, some c818, some c394, some c410, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7656 : lratChecker f7656 p7656 = .success := by decide +kernel
theorem unsat7656 : Unsatisfiable (PosFin 65) f7656 := by
  apply lratCheckerSound f7656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7656
  · intro a ha; simp [p7656] at ha; subst a; trivial
  · exact checked7656
theorem derived7656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7656 := by
  apply localUnsat_implies_entails f7656 [c7528, c798, c799, c796, c818, c394, c410] c7656 unsat7656 (by rfl) a
  have h0 : Entails.eval a c7528 := derived7528 a h
  have h1 : Entails.eval a c798 := h 797 (by decide)
  have h2 : Entails.eval a c799 := h 798 (by decide)
  have h3 : Entails.eval a c796 := h 795 (by decide)
  have h4 : Entails.eval a c818 := h 817 (by decide)
  have h5 : Entails.eval a c394 := h 393 (by decide)
  have h6 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7657 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1128, some c1116, some c1119, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7657 : lratChecker f7657 p7657 = .success := by decide +kernel
theorem unsat7657 : Unsatisfiable (PosFin 65) f7657 := by
  apply lratCheckerSound f7657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7657
  · intro a ha; simp [p7657] at ha; subst a; trivial
  · exact checked7657
theorem derived7657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7657 := by
  apply localUnsat_implies_entails f7657 [c1128, c1116, c1119] c7657 unsat7657 (by rfl) a
  have h0 : Entails.eval a c1128 := h 1127 (by decide)
  have h1 : Entails.eval a c1116 := h 1115 (by decide)
  have h2 : Entails.eval a c1119 := h 1118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7658 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7653, some c7641, some c7655, some c7656, some c7657, some c1126, some c1125, some c1134, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7658 : lratChecker f7658 p7658 = .success := by decide +kernel
theorem unsat7658 : Unsatisfiable (PosFin 65) f7658 := by
  apply lratCheckerSound f7658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7658
  · intro a ha; simp [p7658] at ha; subst a; trivial
  · exact checked7658
theorem derived7658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7658 := by
  apply localUnsat_implies_entails f7658 [c7653, c7641, c7655, c7656, c7657, c1126, c1125, c1134] c7658 unsat7658 (by rfl) a
  have h0 : Entails.eval a c7653 := derived7653 a h
  have h1 : Entails.eval a c7641 := derived7641 a h
  have h2 : Entails.eval a c7655 := derived7655 a h
  have h3 : Entails.eval a c7656 := derived7656 a h
  have h4 : Entails.eval a c7657 := derived7657 a h
  have h5 : Entails.eval a c1126 := h 1125 (by decide)
  have h6 : Entails.eval a c1125 := h 1124 (by decide)
  have h7 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7659 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7528, some c7527, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7659 : lratChecker f7659 p7659 = .success := by decide +kernel
theorem unsat7659 : Unsatisfiable (PosFin 65) f7659 := by
  apply lratCheckerSound f7659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7659
  · intro a ha; simp [p7659] at ha; subst a; trivial
  · exact checked7659
theorem derived7659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7659 := by
  apply localUnsat_implies_entails f7659 [c7528, c7527] c7659 unsat7659 (by rfl) a
  have h0 : Entails.eval a c7528 := derived7528 a h
  have h1 : Entails.eval a c7527 := derived7527 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7660 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7659, some c1114, some c1112, some c1138, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7660 : lratChecker f7660 p7660 = .success := by decide +kernel
theorem unsat7660 : Unsatisfiable (PosFin 65) f7660 := by
  apply lratCheckerSound f7660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7660
  · intro a ha; simp [p7660] at ha; subst a; trivial
  · exact checked7660
theorem derived7660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7660 := by
  apply localUnsat_implies_entails f7660 [c7659, c1114, c1112, c1138] c7660 unsat7660 (by rfl) a
  have h0 : Entails.eval a c7659 := derived7659 a h
  have h1 : Entails.eval a c1114 := h 1113 (by decide)
  have h2 : Entails.eval a c1112 := h 1111 (by decide)
  have h3 : Entails.eval a c1138 := h 1137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7661 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7653, some c7660, some c7658, some c7528, some c798, some c7532, some c796, some c967, some c1064, some c2030, some c2019, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7661 : lratChecker f7661 p7661 = .success := by decide +kernel
theorem unsat7661 : Unsatisfiable (PosFin 65) f7661 := by
  apply lratCheckerSound f7661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7661
  · intro a ha; simp [p7661] at ha; subst a; trivial
  · exact checked7661
theorem derived7661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7661 := by
  apply localUnsat_implies_entails f7661 [c7641, c7653, c7660, c7658, c7528, c798, c7532, c796, c967, c1064, c2030, c2019] c7661 unsat7661 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7653 := derived7653 a h
  have h2 : Entails.eval a c7660 := derived7660 a h
  have h3 : Entails.eval a c7658 := derived7658 a h
  have h4 : Entails.eval a c7528 := derived7528 a h
  have h5 : Entails.eval a c798 := h 797 (by decide)
  have h6 : Entails.eval a c7532 := derived7532 a h
  have h7 : Entails.eval a c796 := h 795 (by decide)
  have h8 : Entails.eval a c967 := h 966 (by decide)
  have h9 : Entails.eval a c1064 := h 1063 (by decide)
  have h10 : Entails.eval a c2030 := h 2029 (by decide)
  have h11 : Entails.eval a c2019 := h 2018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7662 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7653, some c7641, some c7660, some c7533, some c7661, some c7657, some c1126, some c1125, some c1134, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7662 : lratChecker f7662 p7662 = .success := by decide +kernel
theorem unsat7662 : Unsatisfiable (PosFin 65) f7662 := by
  apply lratCheckerSound f7662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7662
  · intro a ha; simp [p7662] at ha; subst a; trivial
  · exact checked7662
theorem derived7662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7662 := by
  apply localUnsat_implies_entails f7662 [c7653, c7641, c7660, c7533, c7661, c7657, c1126, c1125, c1134] c7662 unsat7662 (by rfl) a
  have h0 : Entails.eval a c7653 := derived7653 a h
  have h1 : Entails.eval a c7641 := derived7641 a h
  have h2 : Entails.eval a c7660 := derived7660 a h
  have h3 : Entails.eval a c7533 := derived7533 a h
  have h4 : Entails.eval a c7661 := derived7661 a h
  have h5 : Entails.eval a c7657 := derived7657 a h
  have h6 : Entails.eval a c1126 := h 1125 (by decide)
  have h7 : Entails.eval a c1125 := h 1124 (by decide)
  have h8 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7663 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7321, some c299, some c306, some c305, some c310, some c312, some c304, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p7663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7663 : lratChecker f7663 p7663 = .success := by decide +kernel
theorem unsat7663 : Unsatisfiable (PosFin 65) f7663 := by
  apply lratCheckerSound f7663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7663
  · intro a ha; simp [p7663] at ha; subst a; trivial
  · exact checked7663
theorem derived7663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7663 := by
  apply localUnsat_implies_entails f7663 [c7321, c299, c306, c305, c310, c312, c304] c7663 unsat7663 (by rfl) a
  have h0 : Entails.eval a c7321 := derived7321 a h
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c306 := h 305 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7664 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7662, some c7641, some c793, some c7439, some c1127, some c1142, some c1131, some c1121, some c1109, some c1140, some c2617, some c1830, some c2544, some c1816, some c1232, some c1080, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7664 : lratChecker f7664 p7664 = .success := by decide +kernel
theorem unsat7664 : Unsatisfiable (PosFin 65) f7664 := by
  apply lratCheckerSound f7664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7664
  · intro a ha; simp [p7664] at ha; subst a; trivial
  · exact checked7664
theorem derived7664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7664 := by
  apply localUnsat_implies_entails f7664 [c7662, c7641, c793, c7439, c1127, c1142, c1131, c1121, c1109, c1140, c2617, c1830, c2544, c1816, c1232, c1080] c7664 unsat7664 (by rfl) a
  have h0 : Entails.eval a c7662 := derived7662 a h
  have h1 : Entails.eval a c7641 := derived7641 a h
  have h2 : Entails.eval a c793 := h 792 (by decide)
  have h3 : Entails.eval a c7439 := derived7439 a h
  have h4 : Entails.eval a c1127 := h 1126 (by decide)
  have h5 : Entails.eval a c1142 := h 1141 (by decide)
  have h6 : Entails.eval a c1131 := h 1130 (by decide)
  have h7 : Entails.eval a c1121 := h 1120 (by decide)
  have h8 : Entails.eval a c1109 := h 1108 (by decide)
  have h9 : Entails.eval a c1140 := h 1139 (by decide)
  have h10 : Entails.eval a c2617 := h 2616 (by decide)
  have h11 : Entails.eval a c1830 := h 1829 (by decide)
  have h12 : Entails.eval a c2544 := h 2543 (by decide)
  have h13 : Entails.eval a c1816 := h 1815 (by decide)
  have h14 : Entails.eval a c1232 := h 1231 (by decide)
  have h15 : Entails.eval a c1080 := h 1079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7665 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2536, some c1057, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7665 : lratChecker f7665 p7665 = .success := by decide +kernel
theorem unsat7665 : Unsatisfiable (PosFin 65) f7665 := by
  apply lratCheckerSound f7665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7665
  · intro a ha; simp [p7665] at ha; subst a; trivial
  · exact checked7665
theorem derived7665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7665 := by
  apply localUnsat_implies_entails f7665 [c2536, c1057] c7665 unsat7665 (by rfl) a
  have h0 : Entails.eval a c2536 := h 2535 (by decide)
  have h1 : Entails.eval a c1057 := h 1056 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7666 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7541, some c2019, some c1667, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7666 : lratChecker f7666 p7666 = .success := by decide +kernel
theorem unsat7666 : Unsatisfiable (PosFin 65) f7666 := by
  apply lratCheckerSound f7666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7666
  · intro a ha; simp [p7666] at ha; subst a; trivial
  · exact checked7666
theorem derived7666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7666 := by
  apply localUnsat_implies_entails f7666 [c7541, c2019, c1667] c7666 unsat7666 (by rfl) a
  have h0 : Entails.eval a c7541 := derived7541 a h
  have h1 : Entails.eval a c2019 := h 2018 (by decide)
  have h2 : Entails.eval a c1667 := h 1666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7667 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7664, some c7662, some c7653, some c7641, some c7663, some c787, some c808, some c7640, some c804, some c7637, some c7639, some c811, some c7665, some c7130, some c7666, some c2031, some c1065, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7667 : lratChecker f7667 p7667 = .success := by decide +kernel
theorem unsat7667 : Unsatisfiable (PosFin 65) f7667 := by
  apply lratCheckerSound f7667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7667
  · intro a ha; simp [p7667] at ha; subst a; trivial
  · exact checked7667
theorem derived7667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7667 := by
  apply localUnsat_implies_entails f7667 [c7664, c7662, c7653, c7641, c7663, c787, c808, c7640, c804, c7637, c7639, c811, c7665, c7130, c7666, c2031, c1065] c7667 unsat7667 (by rfl) a
  have h0 : Entails.eval a c7664 := derived7664 a h
  have h1 : Entails.eval a c7662 := derived7662 a h
  have h2 : Entails.eval a c7653 := derived7653 a h
  have h3 : Entails.eval a c7641 := derived7641 a h
  have h4 : Entails.eval a c7663 := derived7663 a h
  have h5 : Entails.eval a c787 := h 786 (by decide)
  have h6 : Entails.eval a c808 := h 807 (by decide)
  have h7 : Entails.eval a c7640 := derived7640 a h
  have h8 : Entails.eval a c804 := h 803 (by decide)
  have h9 : Entails.eval a c7637 := derived7637 a h
  have h10 : Entails.eval a c7639 := derived7639 a h
  have h11 : Entails.eval a c811 := h 810 (by decide)
  have h12 : Entails.eval a c7665 := derived7665 a h
  have h13 : Entails.eval a c7130 := derived7130 a h
  have h14 : Entails.eval a c7666 := derived7666 a h
  have h15 : Entails.eval a c2031 := h 2030 (by decide)
  have h16 : Entails.eval a c1065 := h 1064 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7668 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7641, some c7662, some c7664, some c7667, some c1127, some c1126, some c1125, some c1140, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7668 : lratChecker f7668 p7668 = .success := by decide +kernel
theorem unsat7668 : Unsatisfiable (PosFin 65) f7668 := by
  apply lratCheckerSound f7668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7668
  · intro a ha; simp [p7668] at ha; subst a; trivial
  · exact checked7668
theorem derived7668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7668 := by
  apply localUnsat_implies_entails f7668 [c7641, c7662, c7664, c7667, c1127, c1126, c1125, c1140] c7668 unsat7668 (by rfl) a
  have h0 : Entails.eval a c7641 := derived7641 a h
  have h1 : Entails.eval a c7662 := derived7662 a h
  have h2 : Entails.eval a c7664 := derived7664 a h
  have h3 : Entails.eval a c7667 := derived7667 a h
  have h4 : Entails.eval a c1127 := h 1126 (by decide)
  have h5 : Entails.eval a c1126 := h 1125 (by decide)
  have h6 : Entails.eval a c1125 := h 1124 (by decide)
  have h7 : Entails.eval a c1140 := h 1139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7669 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c335, some c7554, some c7570, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7669 : lratChecker f7669 p7669 = .success := by decide +kernel
theorem unsat7669 : Unsatisfiable (PosFin 65) f7669 := by
  apply lratCheckerSound f7669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7669
  · intro a ha; simp [p7669] at ha; subst a; trivial
  · exact checked7669
theorem derived7669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7669 := by
  apply localUnsat_implies_entails f7669 [c335, c7554, c7570] c7669 unsat7669 (by rfl) a
  have h0 : Entails.eval a c335 := h 334 (by decide)
  have h1 : Entails.eval a c7554 := derived7554 a h
  have h2 : Entails.eval a c7570 := derived7570 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7670 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7557, some c1342, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p7670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7670 : lratChecker f7670 p7670 = .success := by decide +kernel
theorem unsat7670 : Unsatisfiable (PosFin 65) f7670 := by
  apply lratCheckerSound f7670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7670
  · intro a ha; simp [p7670] at ha; subst a; trivial
  · exact checked7670
theorem derived7670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7670 := by
  apply localUnsat_implies_entails f7670 [c7557, c1342] c7670 unsat7670 (by rfl) a
  have h0 : Entails.eval a c7557 := derived7557 a h
  have h1 : Entails.eval a c1342 := h 1341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7671 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7669, some c7340, some c7670, some c1341, some c7618, some c7130, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7671 : lratChecker f7671 p7671 = .success := by decide +kernel
theorem unsat7671 : Unsatisfiable (PosFin 65) f7671 := by
  apply lratCheckerSound f7671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7671
  · intro a ha; simp [p7671] at ha; subst a; trivial
  · exact checked7671
theorem derived7671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7671 := by
  apply localUnsat_implies_entails f7671 [c7669, c7340, c7670, c1341, c7618, c7130] c7671 unsat7671 (by rfl) a
  have h0 : Entails.eval a c7669 := derived7669 a h
  have h1 : Entails.eval a c7340 := derived7340 a h
  have h2 : Entails.eval a c7670 := derived7670 a h
  have h3 : Entails.eval a c1341 := h 1340 (by decide)
  have h4 : Entails.eval a c7618 := derived7618 a h
  have h5 : Entails.eval a c7130 := derived7130 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7672 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1468, some c1506, some c1218, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7672 : lratChecker f7672 p7672 = .success := by decide +kernel
theorem unsat7672 : Unsatisfiable (PosFin 65) f7672 := by
  apply lratCheckerSound f7672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7672
  · intro a ha; simp [p7672] at ha; subst a; trivial
  · exact checked7672
theorem derived7672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7672 := by
  apply localUnsat_implies_entails f7672 [c1468, c1506, c1218] c7672 unsat7672 (by rfl) a
  have h0 : Entails.eval a c1468 := h 1467 (by decide)
  have h1 : Entails.eval a c1506 := h 1505 (by decide)
  have h2 : Entails.eval a c1218 := h 1217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7673 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7671, some c359, some c342, some c7672, some c1465, some c1501, some c2680, some c2672, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7673 : lratChecker f7673 p7673 = .success := by decide +kernel
theorem unsat7673 : Unsatisfiable (PosFin 65) f7673 := by
  apply lratCheckerSound f7673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7673
  · intro a ha; simp [p7673] at ha; subst a; trivial
  · exact checked7673
theorem derived7673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7673 := by
  apply localUnsat_implies_entails f7673 [c7671, c359, c342, c7672, c1465, c1501, c2680, c2672] c7673 unsat7673 (by rfl) a
  have h0 : Entails.eval a c7671 := derived7671 a h
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  have h3 : Entails.eval a c7672 := derived7672 a h
  have h4 : Entails.eval a c1465 := h 1464 (by decide)
  have h5 : Entails.eval a c1501 := h 1500 (by decide)
  have h6 : Entails.eval a c2680 := h 2679 (by decide)
  have h7 : Entails.eval a c2672 := h 2671 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7674 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1274, some c1411, some c2056, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p7674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7674 : lratChecker f7674 p7674 = .success := by decide +kernel
theorem unsat7674 : Unsatisfiable (PosFin 65) f7674 := by
  apply lratCheckerSound f7674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7674
  · intro a ha; simp [p7674] at ha; subst a; trivial
  · exact checked7674
theorem derived7674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7674 := by
  apply localUnsat_implies_entails f7674 [c1274, c1411, c2056] c7674 unsat7674 (by rfl) a
  have h0 : Entails.eval a c1274 := h 1273 (by decide)
  have h1 : Entails.eval a c1411 := h 1410 (by decide)
  have h2 : Entails.eval a c2056 := h 2055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7675 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7674, some c1290, some c2029, some c2119, some c1085, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7675 : lratChecker f7675 p7675 = .success := by decide +kernel
theorem unsat7675 : Unsatisfiable (PosFin 65) f7675 := by
  apply lratCheckerSound f7675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7675
  · intro a ha; simp [p7675] at ha; subst a; trivial
  · exact checked7675
theorem derived7675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7675 := by
  apply localUnsat_implies_entails f7675 [c7674, c1290, c2029, c2119, c1085] c7675 unsat7675 (by rfl) a
  have h0 : Entails.eval a c7674 := derived7674 a h
  have h1 : Entails.eval a c1290 := h 1289 (by decide)
  have h2 : Entails.eval a c2029 := h 2028 (by decide)
  have h3 : Entails.eval a c2119 := h 2118 (by decide)
  have h4 : Entails.eval a c1085 := h 1084 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7676 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c705, some c718, some c707, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7676 : lratChecker f7676 p7676 = .success := by decide +kernel
theorem unsat7676 : Unsatisfiable (PosFin 65) f7676 := by
  apply lratCheckerSound f7676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7676
  · intro a ha; simp [p7676] at ha; subst a; trivial
  · exact checked7676
theorem derived7676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7676 := by
  apply localUnsat_implies_entails f7676 [c705, c718, c707] c7676 unsat7676 (by rfl) a
  have h0 : Entails.eval a c705 := h 704 (by decide)
  have h1 : Entails.eval a c718 := h 717 (by decide)
  have h2 : Entails.eval a c707 := h 706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7677 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7668, some c7671, some c7673, some c7670, some c7676, some c1443, some c1450, some c1411, some c1449, some c1356, some c1444, some c2438, some c7590, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7677 : lratChecker f7677 p7677 = .success := by decide +kernel
theorem unsat7677 : Unsatisfiable (PosFin 65) f7677 := by
  apply lratCheckerSound f7677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7677
  · intro a ha; simp [p7677] at ha; subst a; trivial
  · exact checked7677
theorem derived7677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7677 := by
  apply localUnsat_implies_entails f7677 [c7668, c7671, c7673, c7670, c7676, c1443, c1450, c1411, c1449, c1356, c1444, c2438, c7590] c7677 unsat7677 (by rfl) a
  have h0 : Entails.eval a c7668 := derived7668 a h
  have h1 : Entails.eval a c7671 := derived7671 a h
  have h2 : Entails.eval a c7673 := derived7673 a h
  have h3 : Entails.eval a c7670 := derived7670 a h
  have h4 : Entails.eval a c7676 := derived7676 a h
  have h5 : Entails.eval a c1443 := h 1442 (by decide)
  have h6 : Entails.eval a c1450 := h 1449 (by decide)
  have h7 : Entails.eval a c1411 := h 1410 (by decide)
  have h8 : Entails.eval a c1449 := h 1448 (by decide)
  have h9 : Entails.eval a c1356 := h 1355 (by decide)
  have h10 : Entails.eval a c1444 := h 1443 (by decide)
  have h11 : Entails.eval a c2438 := h 2437 (by decide)
  have h12 : Entails.eval a c7590 := derived7590 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7678 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1466, some c1502, some c2670, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p7678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7678 : lratChecker f7678 p7678 = .success := by decide +kernel
theorem unsat7678 : Unsatisfiable (PosFin 65) f7678 := by
  apply lratCheckerSound f7678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7678
  · intro a ha; simp [p7678] at ha; subst a; trivial
  · exact checked7678
theorem derived7678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7678 := by
  apply localUnsat_implies_entails f7678 [c1466, c1502, c2670] c7678 unsat7678 (by rfl) a
  have h0 : Entails.eval a c1466 := h 1465 (by decide)
  have h1 : Entails.eval a c1502 := h 1501 (by decide)
  have h2 : Entails.eval a c2670 := h 2669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7679 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7677, some c7668, some c7304, some c361, some c7570, some c352, some c368, some c7678, some c362, some c356, some c357, some c353, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7679 : lratChecker f7679 p7679 = .success := by decide +kernel
theorem unsat7679 : Unsatisfiable (PosFin 65) f7679 := by
  apply lratCheckerSound f7679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7679
  · intro a ha; simp [p7679] at ha; subst a; trivial
  · exact checked7679
theorem derived7679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7679 := by
  apply localUnsat_implies_entails f7679 [c7677, c7668, c7304, c361, c7570, c352, c368, c7678, c362, c356, c357, c353] c7679 unsat7679 (by rfl) a
  have h0 : Entails.eval a c7677 := derived7677 a h
  have h1 : Entails.eval a c7668 := derived7668 a h
  have h2 : Entails.eval a c7304 := derived7304 a h
  have h3 : Entails.eval a c361 := h 360 (by decide)
  have h4 : Entails.eval a c7570 := derived7570 a h
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c7678 := derived7678 a h
  have h8 : Entails.eval a c362 := h 361 (by decide)
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7680 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1274, some c1411, some c1340, some c1960, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p7680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7680 : lratChecker f7680 p7680 = .success := by decide +kernel
theorem unsat7680 : Unsatisfiable (PosFin 65) f7680 := by
  apply lratCheckerSound f7680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7680
  · intro a ha; simp [p7680] at ha; subst a; trivial
  · exact checked7680
theorem derived7680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7680 := by
  apply localUnsat_implies_entails f7680 [c1274, c1411, c1340, c1960] c7680 unsat7680 (by rfl) a
  have h0 : Entails.eval a c1274 := h 1273 (by decide)
  have h1 : Entails.eval a c1411 := h 1410 (by decide)
  have h2 : Entails.eval a c1340 := h 1339 (by decide)
  have h3 : Entails.eval a c1960 := h 1959 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7680

end CochromaticTwenty.Certificates.FixedCore1
