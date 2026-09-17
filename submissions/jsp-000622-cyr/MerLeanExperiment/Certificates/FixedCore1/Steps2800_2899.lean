import MerLeanExperiment.Certificates.FixedCore1.Steps2700_2799

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8681 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8675, some c322, some c294, some c7488, some c324, some c177, some c7159, some c247, some c2132, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8681 : lratChecker f8681 p8681 = .success := by decide +kernel
theorem unsat8681 : Unsatisfiable (PosFin 65) f8681 := by
  apply lratCheckerSound f8681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8681
  · intro a ha; simp [p8681] at ha; subst a; trivial
  · exact checked8681
theorem derived8681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8681 := by
  apply localUnsat_implies_entails f8681 [c8675, c322, c294, c7488, c324, c177, c7159, c247, c2132] c8681 unsat8681 (by rfl) a
  have h0 : Entails.eval a c8675 := derived8675 a h
  have h1 : Entails.eval a c322 := h 321 (by decide)
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c7488 := derived7488 a h
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c177 := h 176 (by decide)
  have h6 : Entails.eval a c7159 := derived7159 a h
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c2132 := h 2131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8682 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c322, some c324, some c312, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8682 : lratChecker f8682 p8682 = .success := by decide +kernel
theorem unsat8682 : Unsatisfiable (PosFin 65) f8682 := by
  apply lratCheckerSound f8682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8682
  · intro a ha; simp [p8682] at ha; subst a; trivial
  · exact checked8682
theorem derived8682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8682 := by
  apply localUnsat_implies_entails f8682 [c322, c324, c312] c8682 unsat8682 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c324 := h 323 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8683 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8672, some c8675, some c7338, some c7606, some c335, some c1470, some c1466, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8683 : lratChecker f8683 p8683 = .success := by decide +kernel
theorem unsat8683 : Unsatisfiable (PosFin 65) f8683 := by
  apply lratCheckerSound f8683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8683
  · intro a ha; simp [p8683] at ha; subst a; trivial
  · exact checked8683
theorem derived8683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8683 := by
  apply localUnsat_implies_entails f8683 [c8672, c8675, c7338, c7606, c335, c1470, c1466] c8683 unsat8683 (by rfl) a
  have h0 : Entails.eval a c8672 := derived8672 a h
  have h1 : Entails.eval a c8675 := derived8675 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  have h3 : Entails.eval a c7606 := derived7606 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c1470 := h 1469 (by decide)
  have h6 : Entails.eval a c1466 := h 1465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8684 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8679, some c8675, some c7338, some c7606, some c335, some c1470, some c1466, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8684 : lratChecker f8684 p8684 = .success := by decide +kernel
theorem unsat8684 : Unsatisfiable (PosFin 65) f8684 := by
  apply lratCheckerSound f8684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8684
  · intro a ha; simp [p8684] at ha; subst a; trivial
  · exact checked8684
theorem derived8684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8684 := by
  apply localUnsat_implies_entails f8684 [c8679, c8675, c7338, c7606, c335, c1470, c1466] c8684 unsat8684 (by rfl) a
  have h0 : Entails.eval a c8679 := derived8679 a h
  have h1 : Entails.eval a c8675 := derived8675 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  have h3 : Entails.eval a c7606 := derived7606 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c1470 := h 1469 (by decide)
  have h6 : Entails.eval a c1466 := h 1465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8685 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8675, some c1242, some c1241, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8685 : lratChecker f8685 p8685 = .success := by decide +kernel
theorem unsat8685 : Unsatisfiable (PosFin 65) f8685 := by
  apply lratCheckerSound f8685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8685
  · intro a ha; simp [p8685] at ha; subst a; trivial
  · exact checked8685
theorem derived8685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8685 := by
  apply localUnsat_implies_entails f8685 [c8675, c1242, c1241] c8685 unsat8685 (by rfl) a
  have h0 : Entails.eval a c8675 := derived8675 a h
  have h1 : Entails.eval a c1242 := h 1241 (by decide)
  have h2 : Entails.eval a c1241 := h 1240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8686 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8685, some c8682, some c7338, some c7606, some c335, some c1470, some c1466, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8686 : lratChecker f8686 p8686 = .success := by decide +kernel
theorem unsat8686 : Unsatisfiable (PosFin 65) f8686 := by
  apply lratCheckerSound f8686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8686
  · intro a ha; simp [p8686] at ha; subst a; trivial
  · exact checked8686
theorem derived8686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8686 := by
  apply localUnsat_implies_entails f8686 [c8685, c8682, c7338, c7606, c335, c1470, c1466] c8686 unsat8686 (by rfl) a
  have h0 : Entails.eval a c8685 := derived8685 a h
  have h1 : Entails.eval a c8682 := derived8682 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  have h3 : Entails.eval a c7606 := derived7606 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c1470 := h 1469 (by decide)
  have h6 : Entails.eval a c1466 := h 1465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8687 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨58, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8673, some c8675, some c8672, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8687 : lratChecker f8687 p8687 = .success := by decide +kernel
theorem unsat8687 : Unsatisfiable (PosFin 65) f8687 := by
  apply lratCheckerSound f8687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8687
  · intro a ha; simp [p8687] at ha; subst a; trivial
  · exact checked8687
theorem derived8687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8687 := by
  apply localUnsat_implies_entails f8687 [c8673, c8675, c8672] c8687 unsat8687 (by rfl) a
  have h0 : Entails.eval a c8673 := derived8673 a h
  have h1 : Entails.eval a c8675 := derived8675 a h
  have h2 : Entails.eval a c8672 := derived8672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8688 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8687, some c8678, some c309, some c1402, some c7338, some c1728, some c7606, some c719, some c2580, some c2585, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8688 : lratChecker f8688 p8688 = .success := by decide +kernel
theorem unsat8688 : Unsatisfiable (PosFin 65) f8688 := by
  apply lratCheckerSound f8688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8688
  · intro a ha; simp [p8688] at ha; subst a; trivial
  · exact checked8688
theorem derived8688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8688 := by
  apply localUnsat_implies_entails f8688 [c8687, c8678, c309, c1402, c7338, c1728, c7606, c719, c2580, c2585] c8688 unsat8688 (by rfl) a
  have h0 : Entails.eval a c8687 := derived8687 a h
  have h1 : Entails.eval a c8678 := derived8678 a h
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c1402 := h 1401 (by decide)
  have h4 : Entails.eval a c7338 := derived7338 a h
  have h5 : Entails.eval a c1728 := h 1727 (by decide)
  have h6 : Entails.eval a c7606 := derived7606 a h
  have h7 : Entails.eval a c719 := h 718 (by decide)
  have h8 : Entails.eval a c2580 := h 2579 (by decide)
  have h9 : Entails.eval a c2585 := h 2584 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8689 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8676, some c8677, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8689 : lratChecker f8689 p8689 = .success := by decide +kernel
theorem unsat8689 : Unsatisfiable (PosFin 65) f8689 := by
  apply lratCheckerSound f8689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8689
  · intro a ha; simp [p8689] at ha; subst a; trivial
  · exact checked8689
theorem derived8689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8689 := by
  apply localUnsat_implies_entails f8689 [c8676, c8677] c8689 unsat8689 (by rfl) a
  have h0 : Entails.eval a c8676 := derived8676 a h
  have h1 : Entails.eval a c8677 := derived8677 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8690 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8683, some c8689, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8690 : lratChecker f8690 p8690 = .success := by decide +kernel
theorem unsat8690 : Unsatisfiable (PosFin 65) f8690 := by
  apply lratCheckerSound f8690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8690
  · intro a ha; simp [p8690] at ha; subst a; trivial
  · exact checked8690
theorem derived8690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8690 := by
  apply localUnsat_implies_entails f8690 [c8683, c8689] c8690 unsat8690 (by rfl) a
  have h0 : Entails.eval a c8683 := derived8683 a h
  have h1 : Entails.eval a c8689 := derived8689 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8691 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨28, by decide⟩, false), (⟨58, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8688, some c8690, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8691 : lratChecker f8691 p8691 = .success := by decide +kernel
theorem unsat8691 : Unsatisfiable (PosFin 65) f8691 := by
  apply lratCheckerSound f8691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8691
  · intro a ha; simp [p8691] at ha; subst a; trivial
  · exact checked8691
theorem derived8691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8691 := by
  apply localUnsat_implies_entails f8691 [c8688, c8690] c8691 unsat8691 (by rfl) a
  have h0 : Entails.eval a c8688 := derived8688 a h
  have h1 : Entails.eval a c8690 := derived8690 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8692 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8670, some c8691, some c8674, some c7430, some c880, some c893, some c883, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8692 : lratChecker f8692 p8692 = .success := by decide +kernel
theorem unsat8692 : Unsatisfiable (PosFin 65) f8692 := by
  apply lratCheckerSound f8692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8692
  · intro a ha; simp [p8692] at ha; subst a; trivial
  · exact checked8692
theorem derived8692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8692 := by
  apply localUnsat_implies_entails f8692 [c8670, c8691, c8674, c7430, c880, c893, c883] c8692 unsat8692 (by rfl) a
  have h0 : Entails.eval a c8670 := derived8670 a h
  have h1 : Entails.eval a c8691 := derived8691 a h
  have h2 : Entails.eval a c8674 := derived8674 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c880 := h 879 (by decide)
  have h5 : Entails.eval a c893 := h 892 (by decide)
  have h6 : Entails.eval a c883 := h 882 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8693 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8680, some c8684, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8693 : lratChecker f8693 p8693 = .success := by decide +kernel
theorem unsat8693 : Unsatisfiable (PosFin 65) f8693 := by
  apply lratCheckerSound f8693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8693
  · intro a ha; simp [p8693] at ha; subst a; trivial
  · exact checked8693
theorem derived8693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8693 := by
  apply localUnsat_implies_entails f8693 [c8680, c8684] c8693 unsat8693 (by rfl) a
  have h0 : Entails.eval a c8680 := derived8680 a h
  have h1 : Entails.eval a c8684 := derived8684 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8694 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7606, some c7549, some c7571, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8694 : lratChecker f8694 p8694 = .success := by decide +kernel
theorem unsat8694 : Unsatisfiable (PosFin 65) f8694 := by
  apply lratCheckerSound f8694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8694
  · intro a ha; simp [p8694] at ha; subst a; trivial
  · exact checked8694
theorem derived8694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8694 := by
  apply localUnsat_implies_entails f8694 [c7606, c7549, c7571] c8694 unsat8694 (by rfl) a
  have h0 : Entails.eval a c7606 := derived7606 a h
  have h1 : Entails.eval a c7549 := derived7549 a h
  have h2 : Entails.eval a c7571 := derived7571 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8695 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8681, some c8682, some c7338, some c8694, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8695 : lratChecker f8695 p8695 = .success := by decide +kernel
theorem unsat8695 : Unsatisfiable (PosFin 65) f8695 := by
  apply lratCheckerSound f8695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8695
  · intro a ha; simp [p8695] at ha; subst a; trivial
  · exact checked8695
theorem derived8695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8695 := by
  apply localUnsat_implies_entails f8695 [c8681, c8682, c7338, c8694] c8695 unsat8695 (by rfl) a
  have h0 : Entails.eval a c8681 := derived8681 a h
  have h1 : Entails.eval a c8682 := derived8682 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  have h3 : Entails.eval a c8694 := derived8694 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8696 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8686, some c8695, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8696 : lratChecker f8696 p8696 = .success := by decide +kernel
theorem unsat8696 : Unsatisfiable (PosFin 65) f8696 := by
  apply lratCheckerSound f8696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8696
  · intro a ha; simp [p8696] at ha; subst a; trivial
  · exact checked8696
theorem derived8696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8696 := by
  apply localUnsat_implies_entails f8696 [c8686, c8695] c8696 unsat8696 (by rfl) a
  have h0 : Entails.eval a c8686 := derived8686 a h
  have h1 : Entails.eval a c8695 := derived8695 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8697 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8693, some c8696, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8697 : lratChecker f8697 p8697 = .success := by decide +kernel
theorem unsat8697 : Unsatisfiable (PosFin 65) f8697 := by
  apply lratCheckerSound f8697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8697
  · intro a ha; simp [p8697] at ha; subst a; trivial
  · exact checked8697
theorem derived8697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8697 := by
  apply localUnsat_implies_entails f8697 [c8693, c8696] c8697 unsat8697 (by rfl) a
  have h0 : Entails.eval a c8693 := derived8693 a h
  have h1 : Entails.eval a c8696 := derived8696 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8698 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7572, some c1275, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p8698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8698 : lratChecker f8698 p8698 = .success := by decide +kernel
theorem unsat8698 : Unsatisfiable (PosFin 65) f8698 := by
  apply lratCheckerSound f8698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8698
  · intro a ha; simp [p8698] at ha; subst a; trivial
  · exact checked8698
theorem derived8698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8698 := by
  apply localUnsat_implies_entails f8698 [c7572, c1275] c8698 unsat8698 (by rfl) a
  have h0 : Entails.eval a c7572 := derived7572 a h
  have h1 : Entails.eval a c1275 := h 1274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8699 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8674, some c7430, some c7549, some c8698, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8699 : lratChecker f8699 p8699 = .success := by decide +kernel
theorem unsat8699 : Unsatisfiable (PosFin 65) f8699 := by
  apply lratCheckerSound f8699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8699
  · intro a ha; simp [p8699] at ha; subst a; trivial
  · exact checked8699
theorem derived8699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8699 := by
  apply localUnsat_implies_entails f8699 [c8674, c7430, c7549, c8698] c8699 unsat8699 (by rfl) a
  have h0 : Entails.eval a c8674 := derived8674 a h
  have h1 : Entails.eval a c7430 := derived7430 a h
  have h2 : Entails.eval a c7549 := derived7549 a h
  have h3 : Entails.eval a c8698 := derived8698 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8700 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8692, some c8697, some c8699, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8700 : lratChecker f8700 p8700 = .success := by decide +kernel
theorem unsat8700 : Unsatisfiable (PosFin 65) f8700 := by
  apply lratCheckerSound f8700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8700
  · intro a ha; simp [p8700] at ha; subst a; trivial
  · exact checked8700
theorem derived8700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8700 := by
  apply localUnsat_implies_entails f8700 [c8692, c8697, c8699] c8700 unsat8700 (by rfl) a
  have h0 : Entails.eval a c8692 := derived8692 a h
  have h1 : Entails.eval a c8697 := derived8697 a h
  have h2 : Entails.eval a c8699 := derived8699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8701 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8671, some c7243, some c7492, some c7564, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8701 : lratChecker f8701 p8701 = .success := by decide +kernel
theorem unsat8701 : Unsatisfiable (PosFin 65) f8701 := by
  apply lratCheckerSound f8701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8701
  · intro a ha; simp [p8701] at ha; subst a; trivial
  · exact checked8701
theorem derived8701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8701 := by
  apply localUnsat_implies_entails f8701 [c8671, c7243, c7492, c7564] c8701 unsat8701 (by rfl) a
  have h0 : Entails.eval a c8671 := derived8671 a h
  have h1 : Entails.eval a c7243 := derived7243 a h
  have h2 : Entails.eval a c7492 := derived7492 a h
  have h3 : Entails.eval a c7564 := derived7564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8702 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨58, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8701, some c8694, some c309, some c7332, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8702 : lratChecker f8702 p8702 = .success := by decide +kernel
theorem unsat8702 : Unsatisfiable (PosFin 65) f8702 := by
  apply lratCheckerSound f8702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8702
  · intro a ha; simp [p8702] at ha; subst a; trivial
  · exact checked8702
theorem derived8702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8702 := by
  apply localUnsat_implies_entails f8702 [c8701, c8694, c309, c7332] c8702 unsat8702 (by rfl) a
  have h0 : Entails.eval a c8701 := derived8701 a h
  have h1 : Entails.eval a c8694 := derived8694 a h
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c7332 := derived7332 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8703 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7243, some c7492, some c7564, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8703 : lratChecker f8703 p8703 = .success := by decide +kernel
theorem unsat8703 : Unsatisfiable (PosFin 65) f8703 := by
  apply lratCheckerSound f8703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8703
  · intro a ha; simp [p8703] at ha; subst a; trivial
  · exact checked8703
theorem derived8703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8703 := by
  apply localUnsat_implies_entails f8703 [c7243, c7492, c7564] c8703 unsat8703 (by rfl) a
  have h0 : Entails.eval a c7243 := derived7243 a h
  have h1 : Entails.eval a c7492 := derived7492 a h
  have h2 : Entails.eval a c7564 := derived7564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8704 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8703, some c8694, some c7338, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8704 : lratChecker f8704 p8704 = .success := by decide +kernel
theorem unsat8704 : Unsatisfiable (PosFin 65) f8704 := by
  apply lratCheckerSound f8704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8704
  · intro a ha; simp [p8704] at ha; subst a; trivial
  · exact checked8704
theorem derived8704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8704 := by
  apply localUnsat_implies_entails f8704 [c8703, c8694, c7338] c8704 unsat8704 (by rfl) a
  have h0 : Entails.eval a c8703 := derived8703 a h
  have h1 : Entails.eval a c8694 := derived8694 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8705 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8704, some c8702, some c8672, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8705 : lratChecker f8705 p8705 = .success := by decide +kernel
theorem unsat8705 : Unsatisfiable (PosFin 65) f8705 := by
  apply lratCheckerSound f8705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8705
  · intro a ha; simp [p8705] at ha; subst a; trivial
  · exact checked8705
theorem derived8705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8705 := by
  apply localUnsat_implies_entails f8705 [c8704, c8702, c8672] c8705 unsat8705 (by rfl) a
  have h0 : Entails.eval a c8704 := derived8704 a h
  have h1 : Entails.eval a c8702 := derived8702 a h
  have h2 : Entails.eval a c8672 := derived8672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8706 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8700, some c8670, some c8704, some c8705, some c8679, some c8682, some c7488, some c7168, some c7172, some c7137, some c7158, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8706 : lratChecker f8706 p8706 = .success := by decide +kernel
theorem unsat8706 : Unsatisfiable (PosFin 65) f8706 := by
  apply lratCheckerSound f8706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8706
  · intro a ha; simp [p8706] at ha; subst a; trivial
  · exact checked8706
theorem derived8706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8706 := by
  apply localUnsat_implies_entails f8706 [c8700, c8670, c8704, c8705, c8679, c8682, c7488, c7168, c7172, c7137, c7158] c8706 unsat8706 (by rfl) a
  have h0 : Entails.eval a c8700 := derived8700 a h
  have h1 : Entails.eval a c8670 := derived8670 a h
  have h2 : Entails.eval a c8704 := derived8704 a h
  have h3 : Entails.eval a c8705 := derived8705 a h
  have h4 : Entails.eval a c8679 := derived8679 a h
  have h5 : Entails.eval a c8682 := derived8682 a h
  have h6 : Entails.eval a c7488 := derived7488 a h
  have h7 : Entails.eval a c7168 := derived7168 a h
  have h8 : Entails.eval a c7172 := derived7172 a h
  have h9 : Entails.eval a c7137 := derived7137 a h
  have h10 : Entails.eval a c7158 := derived7158 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8707 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7368, some c7356, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8707 : lratChecker f8707 p8707 = .success := by decide +kernel
theorem unsat8707 : Unsatisfiable (PosFin 65) f8707 := by
  apply lratCheckerSound f8707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8707
  · intro a ha; simp [p8707] at ha; subst a; trivial
  · exact checked8707
theorem derived8707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8707 := by
  apply localUnsat_implies_entails f8707 [c7368, c7356] c8707 unsat8707 (by rfl) a
  have h0 : Entails.eval a c7368 := derived7368 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8708 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8706, some c8707, some c7492, some c7564, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8708 : lratChecker f8708 p8708 = .success := by decide +kernel
theorem unsat8708 : Unsatisfiable (PosFin 65) f8708 := by
  apply lratCheckerSound f8708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8708
  · intro a ha; simp [p8708] at ha; subst a; trivial
  · exact checked8708
theorem derived8708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8708 := by
  apply localUnsat_implies_entails f8708 [c8706, c8707, c7492, c7564] c8708 unsat8708 (by rfl) a
  have h0 : Entails.eval a c8706 := derived8706 a h
  have h1 : Entails.eval a c8707 := derived8707 a h
  have h2 : Entails.eval a c7492 := derived7492 a h
  have h3 : Entails.eval a c7564 := derived7564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8709 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7549, some c7616, some c7622, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8709 : lratChecker f8709 p8709 = .success := by decide +kernel
theorem unsat8709 : Unsatisfiable (PosFin 65) f8709 := by
  apply lratCheckerSound f8709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8709
  · intro a ha; simp [p8709] at ha; subst a; trivial
  · exact checked8709
theorem derived8709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8709 := by
  apply localUnsat_implies_entails f8709 [c7549, c7616, c7622] c8709 unsat8709 (by rfl) a
  have h0 : Entails.eval a c7549 := derived7549 a h
  have h1 : Entails.eval a c7616 := derived7616 a h
  have h2 : Entails.eval a c7622 := derived7622 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8710 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8700, some c8706, some c8708, some c7430, some c7549, some c8709, some c7618, some c1341, some c7130, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8710 : lratChecker f8710 p8710 = .success := by decide +kernel
theorem unsat8710 : Unsatisfiable (PosFin 65) f8710 := by
  apply lratCheckerSound f8710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8710
  · intro a ha; simp [p8710] at ha; subst a; trivial
  · exact checked8710
theorem derived8710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8710 := by
  apply localUnsat_implies_entails f8710 [c8700, c8706, c8708, c7430, c7549, c8709, c7618, c1341, c7130] c8710 unsat8710 (by rfl) a
  have h0 : Entails.eval a c8700 := derived8700 a h
  have h1 : Entails.eval a c8706 := derived8706 a h
  have h2 : Entails.eval a c8708 := derived8708 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7549 := derived7549 a h
  have h5 : Entails.eval a c8709 := derived8709 a h
  have h6 : Entails.eval a c7618 := derived7618 a h
  have h7 : Entails.eval a c1341 := h 1340 (by decide)
  have h8 : Entails.eval a c7130 := derived7130 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8711 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7377, some c7138, some c311, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8711 : lratChecker f8711 p8711 = .success := by decide +kernel
theorem unsat8711 : Unsatisfiable (PosFin 65) f8711 := by
  apply lratCheckerSound f8711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8711
  · intro a ha; simp [p8711] at ha; subst a; trivial
  · exact checked8711
theorem derived8711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8711 := by
  apply localUnsat_implies_entails f8711 [c7377, c7138, c311] c8711 unsat8711 (by rfl) a
  have h0 : Entails.eval a c7377 := derived7377 a h
  have h1 : Entails.eval a c7138 := derived7138 a h
  have h2 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8712 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7643, some c7669, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p8712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8712 : lratChecker f8712 p8712 = .success := by decide +kernel
theorem unsat8712 : Unsatisfiable (PosFin 65) f8712 := by
  apply lratCheckerSound f8712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8712
  · intro a ha; simp [p8712] at ha; subst a; trivial
  · exact checked8712
theorem derived8712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8712 := by
  apply localUnsat_implies_entails f8712 [c7643, c7669] c8712 unsat8712 (by rfl) a
  have h0 : Entails.eval a c7643 := derived7643 a h
  have h1 : Entails.eval a c7669 := derived7669 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8713 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8711, some c8712, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8713 : lratChecker f8713 p8713 = .success := by decide +kernel
theorem unsat8713 : Unsatisfiable (PosFin 65) f8713 := by
  apply lratCheckerSound f8713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8713
  · intro a ha; simp [p8713] at ha; subst a; trivial
  · exact checked8713
theorem derived8713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8713 := by
  apply localUnsat_implies_entails f8713 [c8711, c8712] c8713 unsat8713 (by rfl) a
  have h0 : Entails.eval a c8711 := derived8711 a h
  have h1 : Entails.eval a c8712 := derived8712 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8714 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7332, some c7174, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8714 : lratChecker f8714 p8714 = .success := by decide +kernel
theorem unsat8714 : Unsatisfiable (PosFin 65) f8714 := by
  apply lratCheckerSound f8714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8714
  · intro a ha; simp [p8714] at ha; subst a; trivial
  · exact checked8714
theorem derived8714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8714 := by
  apply localUnsat_implies_entails f8714 [c7332, c7174] c8714 unsat8714 (by rfl) a
  have h0 : Entails.eval a c7332 := derived7332 a h
  have h1 : Entails.eval a c7174 := derived7174 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8715 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7679, some c7695, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8715 : lratChecker f8715 p8715 = .success := by decide +kernel
theorem unsat8715 : Unsatisfiable (PosFin 65) f8715 := by
  apply lratCheckerSound f8715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8715
  · intro a ha; simp [p8715] at ha; subst a; trivial
  · exact checked8715
theorem derived8715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8715 := by
  apply localUnsat_implies_entails f8715 [c7679, c7695] c8715 unsat8715 (by rfl) a
  have h0 : Entails.eval a c7679 := derived7679 a h
  have h1 : Entails.eval a c7695 := derived7695 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8716 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8713, some c8714, some c8715, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8716 : lratChecker f8716 p8716 = .success := by decide +kernel
theorem unsat8716 : Unsatisfiable (PosFin 65) f8716 := by
  apply lratCheckerSound f8716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8716
  · intro a ha; simp [p8716] at ha; subst a; trivial
  · exact checked8716
theorem derived8716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8716 := by
  apply localUnsat_implies_entails f8716 [c8713, c8714, c8715] c8716 unsat8716 (by rfl) a
  have h0 : Entails.eval a c8713 := derived8713 a h
  have h1 : Entails.eval a c8714 := derived8714 a h
  have h2 : Entails.eval a c8715 := derived8715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8717 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7377, some c7356, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8717 : lratChecker f8717 p8717 = .success := by decide +kernel
theorem unsat8717 : Unsatisfiable (PosFin 65) f8717 := by
  apply lratCheckerSound f8717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8717
  · intro a ha; simp [p8717] at ha; subst a; trivial
  · exact checked8717
theorem derived8717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8717 := by
  apply localUnsat_implies_entails f8717 [c7377, c7356] c8717 unsat8717 (by rfl) a
  have h0 : Entails.eval a c7377 := derived7377 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8718 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8717, some c7468, some c7463, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8718 : lratChecker f8718 p8718 = .success := by decide +kernel
theorem unsat8718 : Unsatisfiable (PosFin 65) f8718 := by
  apply lratCheckerSound f8718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8718
  · intro a ha; simp [p8718] at ha; subst a; trivial
  · exact checked8718
theorem derived8718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8718 := by
  apply localUnsat_implies_entails f8718 [c8717, c7468, c7463] c8718 unsat8718 (by rfl) a
  have h0 : Entails.eval a c8717 := derived8717 a h
  have h1 : Entails.eval a c7468 := derived7468 a h
  have h2 : Entails.eval a c7463 := derived7463 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8719 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7662, some c7671, some c7689, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8719 : lratChecker f8719 p8719 = .success := by decide +kernel
theorem unsat8719 : Unsatisfiable (PosFin 65) f8719 := by
  apply lratCheckerSound f8719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8719
  · intro a ha; simp [p8719] at ha; subst a; trivial
  · exact checked8719
theorem derived8719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8719 := by
  apply localUnsat_implies_entails f8719 [c7662, c7671, c7689] c8719 unsat8719 (by rfl) a
  have h0 : Entails.eval a c7662 := derived7662 a h
  have h1 : Entails.eval a c7671 := derived7671 a h
  have h2 : Entails.eval a c7689 := derived7689 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8720 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8710, some c8716, some c8718, some c7662, some c8719, some c7699, some c7616, some c7618, some c1341, some c2183, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8720 : lratChecker f8720 p8720 = .success := by decide +kernel
theorem unsat8720 : Unsatisfiable (PosFin 65) f8720 := by
  apply lratCheckerSound f8720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8720
  · intro a ha; simp [p8720] at ha; subst a; trivial
  · exact checked8720
theorem derived8720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8720 := by
  apply localUnsat_implies_entails f8720 [c8710, c8716, c8718, c7662, c8719, c7699, c7616, c7618, c1341, c2183] c8720 unsat8720 (by rfl) a
  have h0 : Entails.eval a c8710 := derived8710 a h
  have h1 : Entails.eval a c8716 := derived8716 a h
  have h2 : Entails.eval a c8718 := derived8718 a h
  have h3 : Entails.eval a c7662 := derived7662 a h
  have h4 : Entails.eval a c8719 := derived8719 a h
  have h5 : Entails.eval a c7699 := derived7699 a h
  have h6 : Entails.eval a c7616 := derived7616 a h
  have h7 : Entails.eval a c7618 := derived7618 a h
  have h8 : Entails.eval a c1341 := h 1340 (by decide)
  have h9 : Entails.eval a c2183 := h 2182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8721 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8714, some c7139, some c7567, some c382, some c1790, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8721 : lratChecker f8721 p8721 = .success := by decide +kernel
theorem unsat8721 : Unsatisfiable (PosFin 65) f8721 := by
  apply lratCheckerSound f8721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8721
  · intro a ha; simp [p8721] at ha; subst a; trivial
  · exact checked8721
theorem derived8721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8721 := by
  apply localUnsat_implies_entails f8721 [c8714, c7139, c7567, c382, c1790] c8721 unsat8721 (by rfl) a
  have h0 : Entails.eval a c8714 := derived8714 a h
  have h1 : Entails.eval a c7139 := derived7139 a h
  have h2 : Entails.eval a c7567 := derived7567 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c1790 := h 1789 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8722 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7492, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8722 : lratChecker f8722 p8722 = .success := by decide +kernel
theorem unsat8722 : Unsatisfiable (PosFin 65) f8722 := by
  apply lratCheckerSound f8722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8722
  · intro a ha; simp [p8722] at ha; subst a; trivial
  · exact checked8722
theorem derived8722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8722 := by
  apply localUnsat_implies_entails f8722 [c7569, c7492] c8722 unsat8722 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7492 := derived7492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8723 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7545, some c7294, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8723 : lratChecker f8723 p8723 = .success := by decide +kernel
theorem unsat8723 : Unsatisfiable (PosFin 65) f8723 := by
  apply lratCheckerSound f8723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8723
  · intro a ha; simp [p8723] at ha; subst a; trivial
  · exact checked8723
theorem derived8723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8723 := by
  apply localUnsat_implies_entails f8723 [c7545, c7294] c8723 unsat8723 (by rfl) a
  have h0 : Entails.eval a c7545 := derived7545 a h
  have h1 : Entails.eval a c7294 := derived7294 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8724 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8721, some c8722, some c8723, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8724 : lratChecker f8724 p8724 = .success := by decide +kernel
theorem unsat8724 : Unsatisfiable (PosFin 65) f8724 := by
  apply lratCheckerSound f8724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8724
  · intro a ha; simp [p8724] at ha; subst a; trivial
  · exact checked8724
theorem derived8724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8724 := by
  apply localUnsat_implies_entails f8724 [c8721, c8722, c8723] c8724 unsat8724 (by rfl) a
  have h0 : Entails.eval a c8721 := derived8721 a h
  have h1 : Entails.eval a c8722 := derived8722 a h
  have h2 : Entails.eval a c8723 := derived8723 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8725 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8714, some c8711, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8725 : lratChecker f8725 p8725 = .success := by decide +kernel
theorem unsat8725 : Unsatisfiable (PosFin 65) f8725 := by
  apply lratCheckerSound f8725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8725
  · intro a ha; simp [p8725] at ha; subst a; trivial
  · exact checked8725
theorem derived8725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8725 := by
  apply localUnsat_implies_entails f8725 [c8714, c8711] c8725 unsat8725 (by rfl) a
  have h0 : Entails.eval a c8714 := derived8714 a h
  have h1 : Entails.eval a c8711 := derived8711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8726 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c292, some c323, some c303, some c322, some c291, some c319, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8726 : lratChecker f8726 p8726 = .success := by decide +kernel
theorem unsat8726 : Unsatisfiable (PosFin 65) f8726 := by
  apply lratCheckerSound f8726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8726
  · intro a ha; simp [p8726] at ha; subst a; trivial
  · exact checked8726
theorem derived8726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8726 := by
  apply localUnsat_implies_entails f8726 [c8724, c292, c323, c303, c322, c291, c319] c8726 unsat8726 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8727 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8725, some c7221, some c7222, some c1621, some c977, some c7627, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8727 : lratChecker f8727 p8727 = .success := by decide +kernel
theorem unsat8727 : Unsatisfiable (PosFin 65) f8727 := by
  apply lratCheckerSound f8727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8727
  · intro a ha; simp [p8727] at ha; subst a; trivial
  · exact checked8727
theorem derived8727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8727 := by
  apply localUnsat_implies_entails f8727 [c8724, c8725, c7221, c7222, c1621, c977, c7627] c8727 unsat8727 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8725 := derived8725 a h
  have h2 : Entails.eval a c7221 := derived7221 a h
  have h3 : Entails.eval a c7222 := derived7222 a h
  have h4 : Entails.eval a c1621 := h 1620 (by decide)
  have h5 : Entails.eval a c977 := h 976 (by decide)
  have h6 : Entails.eval a c7627 := derived7627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8728 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8283, some c1725, some c1635, some c1933, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p8728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8728 : lratChecker f8728 p8728 = .success := by decide +kernel
theorem unsat8728 : Unsatisfiable (PosFin 65) f8728 := by
  apply lratCheckerSound f8728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8728
  · intro a ha; simp [p8728] at ha; subst a; trivial
  · exact checked8728
theorem derived8728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8728 := by
  apply localUnsat_implies_entails f8728 [c8283, c1725, c1635, c1933] c8728 unsat8728 (by rfl) a
  have h0 : Entails.eval a c8283 := derived8283 a h
  have h1 : Entails.eval a c1725 := h 1724 (by decide)
  have h2 : Entails.eval a c1635 := h 1634 (by decide)
  have h3 : Entails.eval a c1933 := h 1932 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8729 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1001, some c1021, some c2107, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8729 : lratChecker f8729 p8729 = .success := by decide +kernel
theorem unsat8729 : Unsatisfiable (PosFin 65) f8729 := by
  apply lratCheckerSound f8729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8729
  · intro a ha; simp [p8729] at ha; subst a; trivial
  · exact checked8729
theorem derived8729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8729 := by
  apply localUnsat_implies_entails f8729 [c1001, c1021, c2107] c8729 unsat8729 (by rfl) a
  have h0 : Entails.eval a c1001 := h 1000 (by decide)
  have h1 : Entails.eval a c1021 := h 1020 (by decide)
  have h2 : Entails.eval a c2107 := h 2106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8730 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8729, some c1894, some c1931, some c7256, some c1668, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8730 : lratChecker f8730 p8730 = .success := by decide +kernel
theorem unsat8730 : Unsatisfiable (PosFin 65) f8730 := by
  apply lratCheckerSound f8730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8730
  · intro a ha; simp [p8730] at ha; subst a; trivial
  · exact checked8730
theorem derived8730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8730 := by
  apply localUnsat_implies_entails f8730 [c8729, c1894, c1931, c7256, c1668] c8730 unsat8730 (by rfl) a
  have h0 : Entails.eval a c8729 := derived8729 a h
  have h1 : Entails.eval a c1894 := h 1893 (by decide)
  have h2 : Entails.eval a c1931 := h 1930 (by decide)
  have h3 : Entails.eval a c7256 := derived7256 a h
  have h4 : Entails.eval a c1668 := h 1667 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8731 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8725, some c7722, some c7688, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8731 : lratChecker f8731 p8731 = .success := by decide +kernel
theorem unsat8731 : Unsatisfiable (PosFin 65) f8731 := by
  apply lratCheckerSound f8731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8731
  · intro a ha; simp [p8731] at ha; subst a; trivial
  · exact checked8731
theorem derived8731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8731 := by
  apply localUnsat_implies_entails f8731 [c8724, c8725, c7722, c7688] c8731 unsat8731 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8725 := derived8725 a h
  have h2 : Entails.eval a c7722 := derived7722 a h
  have h3 : Entails.eval a c7688 := derived7688 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8732 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7627, some c359, some c7735, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8732 : lratChecker f8732 p8732 = .success := by decide +kernel
theorem unsat8732 : Unsatisfiable (PosFin 65) f8732 := by
  apply lratCheckerSound f8732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8732
  · intro a ha; simp [p8732] at ha; subst a; trivial
  · exact checked8732
theorem derived8732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8732 := by
  apply localUnsat_implies_entails f8732 [c7627, c359, c7735] c8732 unsat8732 (by rfl) a
  have h0 : Entails.eval a c7627 := derived7627 a h
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c7735 := derived7735 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8733 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1735, some c1394, some c1223, some c1636, some c134, some c8166, some c148, some c6777, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8733 : lratChecker f8733 p8733 = .success := by decide +kernel
theorem unsat8733 : Unsatisfiable (PosFin 65) f8733 := by
  apply lratCheckerSound f8733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8733
  · intro a ha; simp [p8733] at ha; subst a; trivial
  · exact checked8733
theorem derived8733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8733 := by
  apply localUnsat_implies_entails f8733 [c1735, c1394, c1223, c1636, c134, c8166, c148, c6777] c8733 unsat8733 (by rfl) a
  have h0 : Entails.eval a c1735 := h 1734 (by decide)
  have h1 : Entails.eval a c1394 := h 1393 (by decide)
  have h2 : Entails.eval a c1223 := h 1222 (by decide)
  have h3 : Entails.eval a c1636 := h 1635 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c8166 := derived8166 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c6777 := derived6777 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8734 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1646, some c1737, some c139, some c147, some c6776, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8734 : lratChecker f8734 p8734 = .success := by decide +kernel
theorem unsat8734 : Unsatisfiable (PosFin 65) f8734 := by
  apply lratCheckerSound f8734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8734
  · intro a ha; simp [p8734] at ha; subst a; trivial
  · exact checked8734
theorem derived8734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8734 := by
  apply localUnsat_implies_entails f8734 [c1646, c1737, c139, c147, c6776] c8734 unsat8734 (by rfl) a
  have h0 : Entails.eval a c1646 := h 1645 (by decide)
  have h1 : Entails.eval a c1737 := h 1736 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c6776 := derived6776 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8735 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8720, some c8724, some c8731, some c8732, some c8725, some c8726, some c8727, some c8730, some c8734, some c1735, some c1394, some c1221, some c134, some c8166, some c1986, some c1648, some c7256, some c148, some c6663, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8735 : lratChecker f8735 p8735 = .success := by decide +kernel
theorem unsat8735 : Unsatisfiable (PosFin 65) f8735 := by
  apply lratCheckerSound f8735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8735
  · intro a ha; simp [p8735] at ha; subst a; trivial
  · exact checked8735
theorem derived8735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8735 := by
  apply localUnsat_implies_entails f8735 [c8720, c8724, c8731, c8732, c8725, c8726, c8727, c8730, c8734, c1735, c1394, c1221, c134, c8166, c1986, c1648, c7256, c148, c6663] c8735 unsat8735 (by rfl) a
  have h0 : Entails.eval a c8720 := derived8720 a h
  have h1 : Entails.eval a c8724 := derived8724 a h
  have h2 : Entails.eval a c8731 := derived8731 a h
  have h3 : Entails.eval a c8732 := derived8732 a h
  have h4 : Entails.eval a c8725 := derived8725 a h
  have h5 : Entails.eval a c8726 := derived8726 a h
  have h6 : Entails.eval a c8727 := derived8727 a h
  have h7 : Entails.eval a c8730 := derived8730 a h
  have h8 : Entails.eval a c8734 := derived8734 a h
  have h9 : Entails.eval a c1735 := h 1734 (by decide)
  have h10 : Entails.eval a c1394 := h 1393 (by decide)
  have h11 : Entails.eval a c1221 := h 1220 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c8166 := derived8166 a h
  have h14 : Entails.eval a c1986 := h 1985 (by decide)
  have h15 : Entails.eval a c1648 := h 1647 (by decide)
  have h16 : Entails.eval a c7256 := derived7256 a h
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c6663 := derived6663 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8736 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1737, some c1957, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8736 : lratChecker f8736 p8736 = .success := by decide +kernel
theorem unsat8736 : Unsatisfiable (PosFin 65) f8736 := by
  apply lratCheckerSound f8736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8736
  · intro a ha; simp [p8736] at ha; subst a; trivial
  · exact checked8736
theorem derived8736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8736 := by
  apply localUnsat_implies_entails f8736 [c1737, c1957] c8736 unsat8736 (by rfl) a
  have h0 : Entails.eval a c1737 := h 1736 (by decide)
  have h1 : Entails.eval a c1957 := h 1956 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8737 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8720, some c8724, some c8725, some c8726, some c8727, some c8731, some c8730, some c8732, some c8735, some c8736, some c1735, some c1932, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8737 : lratChecker f8737 p8737 = .success := by decide +kernel
theorem unsat8737 : Unsatisfiable (PosFin 65) f8737 := by
  apply lratCheckerSound f8737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8737
  · intro a ha; simp [p8737] at ha; subst a; trivial
  · exact checked8737
theorem derived8737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8737 := by
  apply localUnsat_implies_entails f8737 [c8720, c8724, c8725, c8726, c8727, c8731, c8730, c8732, c8735, c8736, c1735, c1932] c8737 unsat8737 (by rfl) a
  have h0 : Entails.eval a c8720 := derived8720 a h
  have h1 : Entails.eval a c8724 := derived8724 a h
  have h2 : Entails.eval a c8725 := derived8725 a h
  have h3 : Entails.eval a c8726 := derived8726 a h
  have h4 : Entails.eval a c8727 := derived8727 a h
  have h5 : Entails.eval a c8731 := derived8731 a h
  have h6 : Entails.eval a c8730 := derived8730 a h
  have h7 : Entails.eval a c8732 := derived8732 a h
  have h8 : Entails.eval a c8735 := derived8735 a h
  have h9 : Entails.eval a c8736 := derived8736 a h
  have h10 : Entails.eval a c1735 := h 1734 (by decide)
  have h11 : Entails.eval a c1932 := h 1931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8738 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c321, some c290, some c303, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8738 : lratChecker f8738 p8738 = .success := by decide +kernel
theorem unsat8738 : Unsatisfiable (PosFin 65) f8738 := by
  apply lratCheckerSound f8738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8738
  · intro a ha; simp [p8738] at ha; subst a; trivial
  · exact checked8738
theorem derived8738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8738 := by
  apply localUnsat_implies_entails f8738 [c321, c290, c303] c8738 unsat8738 (by rfl) a
  have h0 : Entails.eval a c321 := h 320 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8739 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8738, some c309, some c313, some c319, some c315, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8739 : lratChecker f8739 p8739 = .success := by decide +kernel
theorem unsat8739 : Unsatisfiable (PosFin 65) f8739 := by
  apply lratCheckerSound f8739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8739
  · intro a ha; simp [p8739] at ha; subst a; trivial
  · exact checked8739
theorem derived8739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8739 := by
  apply localUnsat_implies_entails f8739 [c8724, c8738, c309, c313, c319, c315] c8739 unsat8739 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8738 := derived8738 a h
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8740 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7739, some c373, some c370, some c376, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8740 : lratChecker f8740 p8740 = .success := by decide +kernel
theorem unsat8740 : Unsatisfiable (PosFin 65) f8740 := by
  apply lratCheckerSound f8740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8740
  · intro a ha; simp [p8740] at ha; subst a; trivial
  · exact checked8740
theorem derived8740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8740 := by
  apply localUnsat_implies_entails f8740 [c7739, c373, c370, c376] c8740 unsat8740 (by rfl) a
  have h0 : Entails.eval a c7739 := derived7739 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8741 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6695, some c6693, some c6694, some c374, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8741 : lratChecker f8741 p8741 = .success := by decide +kernel
theorem unsat8741 : Unsatisfiable (PosFin 65) f8741 := by
  apply lratCheckerSound f8741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8741
  · intro a ha; simp [p8741] at ha; subst a; trivial
  · exact checked8741
theorem derived8741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8741 := by
  apply localUnsat_implies_entails f8741 [c6695, c6693, c6694, c374] c8741 unsat8741 (by rfl) a
  have h0 : Entails.eval a c6695 := derived6695 a h
  have h1 : Entails.eval a c6693 := derived6693 a h
  have h2 : Entails.eval a c6694 := derived6694 a h
  have h3 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8742 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8740, some c8741, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8742 : lratChecker f8742 p8742 = .success := by decide +kernel
theorem unsat8742 : Unsatisfiable (PosFin 65) f8742 := by
  apply lratCheckerSound f8742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8742
  · intro a ha; simp [p8742] at ha; subst a; trivial
  · exact checked8742
theorem derived8742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8742 := by
  apply localUnsat_implies_entails f8742 [c8740, c8741] c8742 unsat8742 (by rfl) a
  have h0 : Entails.eval a c8740 := derived8740 a h
  have h1 : Entails.eval a c8741 := derived8741 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8743 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨6, by decide⟩, false), (⟨58, by decide⟩, false), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c59, some c64, some c6681, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p8743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8743 : lratChecker f8743 p8743 = .success := by decide +kernel
theorem unsat8743 : Unsatisfiable (PosFin 65) f8743 := by
  apply lratCheckerSound f8743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8743
  · intro a ha; simp [p8743] at ha; subst a; trivial
  · exact checked8743
theorem derived8743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8743 := by
  apply localUnsat_implies_entails f8743 [c59, c64, c6681] c8743 unsat8743 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c6681 := derived6681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8744 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨26, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8725, some c7777, some c8739, some c970, some c990, some c1614, some c8292, some c7780, some c1584, some c1600, some c1393, some c813, some c1745, some c1663, some c2366, some c1801, some c2531, some c8743, some c6664, some c6674, some c163, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8744 : lratChecker f8744 p8744 = .success := by decide +kernel
theorem unsat8744 : Unsatisfiable (PosFin 65) f8744 := by
  apply lratCheckerSound f8744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8744
  · intro a ha; simp [p8744] at ha; subst a; trivial
  · exact checked8744
theorem derived8744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8744 := by
  apply localUnsat_implies_entails f8744 [c8724, c8725, c7777, c8739, c970, c990, c1614, c8292, c7780, c1584, c1600, c1393, c813, c1745, c1663, c2366, c1801, c2531, c8743, c6664, c6674, c163] c8744 unsat8744 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8725 := derived8725 a h
  have h2 : Entails.eval a c7777 := derived7777 a h
  have h3 : Entails.eval a c8739 := derived8739 a h
  have h4 : Entails.eval a c970 := h 969 (by decide)
  have h5 : Entails.eval a c990 := h 989 (by decide)
  have h6 : Entails.eval a c1614 := h 1613 (by decide)
  have h7 : Entails.eval a c8292 := derived8292 a h
  have h8 : Entails.eval a c7780 := derived7780 a h
  have h9 : Entails.eval a c1584 := h 1583 (by decide)
  have h10 : Entails.eval a c1600 := h 1599 (by decide)
  have h11 : Entails.eval a c1393 := h 1392 (by decide)
  have h12 : Entails.eval a c813 := h 812 (by decide)
  have h13 : Entails.eval a c1745 := h 1744 (by decide)
  have h14 : Entails.eval a c1663 := h 1662 (by decide)
  have h15 : Entails.eval a c2366 := h 2365 (by decide)
  have h16 : Entails.eval a c1801 := h 1800 (by decide)
  have h17 : Entails.eval a c2531 := h 2530 (by decide)
  have h18 : Entails.eval a c8743 := derived8743 a h
  have h19 : Entails.eval a c6664 := derived6664 a h
  have h20 : Entails.eval a c6674 := derived6674 a h
  have h21 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8745 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8725, some c7777, some c8739, some c8744, some c8729, some c1894, some c1931, some c1671, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8745 : lratChecker f8745 p8745 = .success := by decide +kernel
theorem unsat8745 : Unsatisfiable (PosFin 65) f8745 := by
  apply lratCheckerSound f8745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8745
  · intro a ha; simp [p8745] at ha; subst a; trivial
  · exact checked8745
theorem derived8745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8745 := by
  apply localUnsat_implies_entails f8745 [c8724, c8725, c7777, c8739, c8744, c8729, c1894, c1931, c1671] c8745 unsat8745 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8725 := derived8725 a h
  have h2 : Entails.eval a c7777 := derived7777 a h
  have h3 : Entails.eval a c8739 := derived8739 a h
  have h4 : Entails.eval a c8744 := derived8744 a h
  have h5 : Entails.eval a c8729 := derived8729 a h
  have h6 : Entails.eval a c1894 := h 1893 (by decide)
  have h7 : Entails.eval a c1931 := h 1930 (by decide)
  have h8 : Entails.eval a c1671 := h 1670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8746 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8745, some c8724, some c8725, some c7777, some c8739, some c970, some c8292, some c8677, some c7780, some c1627, some c1584, some c1600, some c1405, some c818, some c1594, some c1801, some c1665, some c1065, some c8743, some c6664, some c6674, some c1781, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8746 : lratChecker f8746 p8746 = .success := by decide +kernel
theorem unsat8746 : Unsatisfiable (PosFin 65) f8746 := by
  apply lratCheckerSound f8746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8746
  · intro a ha; simp [p8746] at ha; subst a; trivial
  · exact checked8746
theorem derived8746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8746 := by
  apply localUnsat_implies_entails f8746 [c8745, c8724, c8725, c7777, c8739, c970, c8292, c8677, c7780, c1627, c1584, c1600, c1405, c818, c1594, c1801, c1665, c1065, c8743, c6664, c6674, c1781] c8746 unsat8746 (by rfl) a
  have h0 : Entails.eval a c8745 := derived8745 a h
  have h1 : Entails.eval a c8724 := derived8724 a h
  have h2 : Entails.eval a c8725 := derived8725 a h
  have h3 : Entails.eval a c7777 := derived7777 a h
  have h4 : Entails.eval a c8739 := derived8739 a h
  have h5 : Entails.eval a c970 := h 969 (by decide)
  have h6 : Entails.eval a c8292 := derived8292 a h
  have h7 : Entails.eval a c8677 := derived8677 a h
  have h8 : Entails.eval a c7780 := derived7780 a h
  have h9 : Entails.eval a c1627 := h 1626 (by decide)
  have h10 : Entails.eval a c1584 := h 1583 (by decide)
  have h11 : Entails.eval a c1600 := h 1599 (by decide)
  have h12 : Entails.eval a c1405 := h 1404 (by decide)
  have h13 : Entails.eval a c818 := h 817 (by decide)
  have h14 : Entails.eval a c1594 := h 1593 (by decide)
  have h15 : Entails.eval a c1801 := h 1800 (by decide)
  have h16 : Entails.eval a c1665 := h 1664 (by decide)
  have h17 : Entails.eval a c1065 := h 1064 (by decide)
  have h18 : Entails.eval a c8743 := derived8743 a h
  have h19 : Entails.eval a c6664 := derived6664 a h
  have h20 : Entails.eval a c6674 := derived6674 a h
  have h21 : Entails.eval a c1781 := h 1780 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8747 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8739, some c8724, some c8725, some c7780, some c1924, some c1951, some c1676, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8747 : lratChecker f8747 p8747 = .success := by decide +kernel
theorem unsat8747 : Unsatisfiable (PosFin 65) f8747 := by
  apply lratCheckerSound f8747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8747
  · intro a ha; simp [p8747] at ha; subst a; trivial
  · exact checked8747
theorem derived8747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8747 := by
  apply localUnsat_implies_entails f8747 [c8739, c8724, c8725, c7780, c1924, c1951, c1676] c8747 unsat8747 (by rfl) a
  have h0 : Entails.eval a c8739 := derived8739 a h
  have h1 : Entails.eval a c8724 := derived8724 a h
  have h2 : Entails.eval a c8725 := derived8725 a h
  have h3 : Entails.eval a c7780 := derived7780 a h
  have h4 : Entails.eval a c1924 := h 1923 (by decide)
  have h5 : Entails.eval a c1951 := h 1950 (by decide)
  have h6 : Entails.eval a c1676 := h 1675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8748 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8724, some c8725, some c7777, some c8739, some c8747, some c1735, some c1932, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8748 : lratChecker f8748 p8748 = .success := by decide +kernel
theorem unsat8748 : Unsatisfiable (PosFin 65) f8748 := by
  apply lratCheckerSound f8748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8748
  · intro a ha; simp [p8748] at ha; subst a; trivial
  · exact checked8748
theorem derived8748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8748 := by
  apply localUnsat_implies_entails f8748 [c8724, c8725, c7777, c8739, c8747, c1735, c1932] c8748 unsat8748 (by rfl) a
  have h0 : Entails.eval a c8724 := derived8724 a h
  have h1 : Entails.eval a c8725 := derived8725 a h
  have h2 : Entails.eval a c7777 := derived7777 a h
  have h3 : Entails.eval a c8739 := derived8739 a h
  have h4 : Entails.eval a c8747 := derived8747 a h
  have h5 : Entails.eval a c1735 := h 1734 (by decide)
  have h6 : Entails.eval a c1932 := h 1931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8749 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8739, some c8724, some c8725, some c7780, some c7781, some c1009, some c7316, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8749 : lratChecker f8749 p8749 = .success := by decide +kernel
theorem unsat8749 : Unsatisfiable (PosFin 65) f8749 := by
  apply lratCheckerSound f8749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8749
  · intro a ha; simp [p8749] at ha; subst a; trivial
  · exact checked8749
theorem derived8749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8749 := by
  apply localUnsat_implies_entails f8749 [c8739, c8724, c8725, c7780, c7781, c1009, c7316] c8749 unsat8749 (by rfl) a
  have h0 : Entails.eval a c8739 := derived8739 a h
  have h1 : Entails.eval a c8724 := derived8724 a h
  have h2 : Entails.eval a c8725 := derived8725 a h
  have h3 : Entails.eval a c7780 := derived7780 a h
  have h4 : Entails.eval a c7781 := derived7781 a h
  have h5 : Entails.eval a c1009 := h 1008 (by decide)
  have h6 : Entails.eval a c7316 := derived7316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8750 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8720, some c8670, some c8724, some c8725, some c8737, some c8739, some c8742, some c7777, some c8745, some c8746, some c8748, some c8749, some c1735, some c1394, some c1221, some c134, some c8733, some c2043, some c8166, some c1986, some c1648, some c1724, some c8358, some c148, some c7656, some c1005, some c1153, some c6723, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked8750 : lratChecker f8750 p8750 = .success := by decide +kernel
theorem unsat8750 : Unsatisfiable (PosFin 65) f8750 := by
  apply lratCheckerSound f8750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8750
  · intro a ha; simp [p8750] at ha; subst a; trivial
  · exact checked8750
theorem derived8750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8750 := by
  apply localUnsat_implies_entails f8750 [c8720, c8670, c8724, c8725, c8737, c8739, c8742, c7777, c8745, c8746, c8748, c8749, c1735, c1394, c1221, c134, c8733, c2043, c8166, c1986, c1648, c1724, c8358, c148, c7656, c1005, c1153, c6723] c8750 unsat8750 (by rfl) a
  have h0 : Entails.eval a c8720 := derived8720 a h
  have h1 : Entails.eval a c8670 := derived8670 a h
  have h2 : Entails.eval a c8724 := derived8724 a h
  have h3 : Entails.eval a c8725 := derived8725 a h
  have h4 : Entails.eval a c8737 := derived8737 a h
  have h5 : Entails.eval a c8739 := derived8739 a h
  have h6 : Entails.eval a c8742 := derived8742 a h
  have h7 : Entails.eval a c7777 := derived7777 a h
  have h8 : Entails.eval a c8745 := derived8745 a h
  have h9 : Entails.eval a c8746 := derived8746 a h
  have h10 : Entails.eval a c8748 := derived8748 a h
  have h11 : Entails.eval a c8749 := derived8749 a h
  have h12 : Entails.eval a c1735 := h 1734 (by decide)
  have h13 : Entails.eval a c1394 := h 1393 (by decide)
  have h14 : Entails.eval a c1221 := h 1220 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c8733 := derived8733 a h
  have h17 : Entails.eval a c2043 := h 2042 (by decide)
  have h18 : Entails.eval a c8166 := derived8166 a h
  have h19 : Entails.eval a c1986 := h 1985 (by decide)
  have h20 : Entails.eval a c1648 := h 1647 (by decide)
  have h21 : Entails.eval a c1724 := h 1723 (by decide)
  have h22 : Entails.eval a c8358 := derived8358 a h
  have h23 : Entails.eval a c148 := h 147 (by decide)
  have h24 : Entails.eval a c7656 := derived7656 a h
  have h25 : Entails.eval a c1005 := h 1004 (by decide)
  have h26 : Entails.eval a c1153 := h 1152 (by decide)
  have h27 : Entails.eval a c6723 := derived6723 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8751 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8718, some c7763, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8751 : lratChecker f8751 p8751 = .success := by decide +kernel
theorem unsat8751 : Unsatisfiable (PosFin 65) f8751 := by
  apply lratCheckerSound f8751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8751
  · intro a ha; simp [p8751] at ha; subst a; trivial
  · exact checked8751
theorem derived8751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8751 := by
  apply localUnsat_implies_entails f8751 [c8718, c7763] c8751 unsat8751 (by rfl) a
  have h0 : Entails.eval a c8718 := derived8718 a h
  have h1 : Entails.eval a c7763 := derived7763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8752 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8751, some c7430, some c7549, some c7621, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8752 : lratChecker f8752 p8752 = .success := by decide +kernel
theorem unsat8752 : Unsatisfiable (PosFin 65) f8752 := by
  apply lratCheckerSound f8752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8752
  · intro a ha; simp [p8752] at ha; subst a; trivial
  · exact checked8752
theorem derived8752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8752 := by
  apply localUnsat_implies_entails f8752 [c8751, c7430, c7549, c7621] c8752 unsat8752 (by rfl) a
  have h0 : Entails.eval a c8751 := derived8751 a h
  have h1 : Entails.eval a c7430 := derived7430 a h
  have h2 : Entails.eval a c7549 := derived7549 a h
  have h3 : Entails.eval a c7621 := derived7621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8753 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7812, some c7795, some c970, some c1058, some c903, some c1932, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8753 : lratChecker f8753 p8753 = .success := by decide +kernel
theorem unsat8753 : Unsatisfiable (PosFin 65) f8753 := by
  apply lratCheckerSound f8753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8753
  · intro a ha; simp [p8753] at ha; subst a; trivial
  · exact checked8753
theorem derived8753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8753 := by
  apply localUnsat_implies_entails f8753 [c7812, c7795, c970, c1058, c903, c1932] c8753 unsat8753 (by rfl) a
  have h0 : Entails.eval a c7812 := derived7812 a h
  have h1 : Entails.eval a c7795 := derived7795 a h
  have h2 : Entails.eval a c970 := h 969 (by decide)
  have h3 : Entails.eval a c1058 := h 1057 (by decide)
  have h4 : Entails.eval a c903 := h 902 (by decide)
  have h5 : Entails.eval a c1932 := h 1931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8754 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8720, some c8750, some c8752, some c8718, some c8753, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8754 : lratChecker f8754 p8754 = .success := by decide +kernel
theorem unsat8754 : Unsatisfiable (PosFin 65) f8754 := by
  apply lratCheckerSound f8754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8754
  · intro a ha; simp [p8754] at ha; subst a; trivial
  · exact checked8754
theorem derived8754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8754 := by
  apply localUnsat_implies_entails f8754 [c8720, c8750, c8752, c8718, c8753] c8754 unsat8754 (by rfl) a
  have h0 : Entails.eval a c8720 := derived8720 a h
  have h1 : Entails.eval a c8750 := derived8750 a h
  have h2 : Entails.eval a c8752 := derived8752 a h
  have h3 : Entails.eval a c8718 := derived8718 a h
  have h4 : Entails.eval a c8753 := derived8753 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8755 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8750, some c8720, some c8754, some c7430, some c7549, some c7617, some c7625, some c1351, some c1967, some c7623, some c1310, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8755 : lratChecker f8755 p8755 = .success := by decide +kernel
theorem unsat8755 : Unsatisfiable (PosFin 65) f8755 := by
  apply lratCheckerSound f8755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8755
  · intro a ha; simp [p8755] at ha; subst a; trivial
  · exact checked8755
theorem derived8755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8755 := by
  apply localUnsat_implies_entails f8755 [c8750, c8720, c8754, c7430, c7549, c7617, c7625, c1351, c1967, c7623, c1310] c8755 unsat8755 (by rfl) a
  have h0 : Entails.eval a c8750 := derived8750 a h
  have h1 : Entails.eval a c8720 := derived8720 a h
  have h2 : Entails.eval a c8754 := derived8754 a h
  have h3 : Entails.eval a c7430 := derived7430 a h
  have h4 : Entails.eval a c7549 := derived7549 a h
  have h5 : Entails.eval a c7617 := derived7617 a h
  have h6 : Entails.eval a c7625 := derived7625 a h
  have h7 : Entails.eval a c1351 := h 1350 (by decide)
  have h8 : Entails.eval a c1967 := h 1966 (by decide)
  have h9 : Entails.eval a c7623 := derived7623 a h
  have h10 : Entails.eval a c1310 := h 1309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8756 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7627, some c7355, some c7670, some c903, some c8019, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8756 : lratChecker f8756 p8756 = .success := by decide +kernel
theorem unsat8756 : Unsatisfiable (PosFin 65) f8756 := by
  apply lratCheckerSound f8756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8756
  · intro a ha; simp [p8756] at ha; subst a; trivial
  · exact checked8756
theorem derived8756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8756 := by
  apply localUnsat_implies_entails f8756 [c7627, c7355, c7670, c903, c8019] c8756 unsat8756 (by rfl) a
  have h0 : Entails.eval a c7627 := derived7627 a h
  have h1 : Entails.eval a c7355 := derived7355 a h
  have h2 : Entails.eval a c7670 := derived7670 a h
  have h3 : Entails.eval a c903 := h 902 (by decide)
  have h4 : Entails.eval a c8019 := derived8019 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8757 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7688, some c882, some c970, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8757 : lratChecker f8757 p8757 = .success := by decide +kernel
theorem unsat8757 : Unsatisfiable (PosFin 65) f8757 := by
  apply lratCheckerSound f8757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8757
  · intro a ha; simp [p8757] at ha; subst a; trivial
  · exact checked8757
theorem derived8757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8757 := by
  apply localUnsat_implies_entails f8757 [c7688, c882, c970] c8757 unsat8757 (by rfl) a
  have h0 : Entails.eval a c7688 := derived7688 a h
  have h1 : Entails.eval a c882 := h 881 (by decide)
  have h2 : Entails.eval a c970 := h 969 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8758 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8756, some c8757, some c7688, some c7618, some c1073, some c7805, some c7808, some c1957, some c1953, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8758 : lratChecker f8758 p8758 = .success := by decide +kernel
theorem unsat8758 : Unsatisfiable (PosFin 65) f8758 := by
  apply lratCheckerSound f8758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8758
  · intro a ha; simp [p8758] at ha; subst a; trivial
  · exact checked8758
theorem derived8758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8758 := by
  apply localUnsat_implies_entails f8758 [c8756, c8757, c7688, c7618, c1073, c7805, c7808, c1957, c1953] c8758 unsat8758 (by rfl) a
  have h0 : Entails.eval a c8756 := derived8756 a h
  have h1 : Entails.eval a c8757 := derived8757 a h
  have h2 : Entails.eval a c7688 := derived7688 a h
  have h3 : Entails.eval a c7618 := derived7618 a h
  have h4 : Entails.eval a c1073 := h 1072 (by decide)
  have h5 : Entails.eval a c7805 := derived7805 a h
  have h6 : Entails.eval a c7808 := derived7808 a h
  have h7 : Entails.eval a c1957 := h 1956 (by decide)
  have h8 : Entails.eval a c1953 := h 1952 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8759 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8756, some c7688, some c7618, some c8757, some c8758, some c1058, some c1932, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8759 : lratChecker f8759 p8759 = .success := by decide +kernel
theorem unsat8759 : Unsatisfiable (PosFin 65) f8759 := by
  apply lratCheckerSound f8759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8759
  · intro a ha; simp [p8759] at ha; subst a; trivial
  · exact checked8759
theorem derived8759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8759 := by
  apply localUnsat_implies_entails f8759 [c8756, c7688, c7618, c8757, c8758, c1058, c1932] c8759 unsat8759 (by rfl) a
  have h0 : Entails.eval a c8756 := derived8756 a h
  have h1 : Entails.eval a c7688 := derived7688 a h
  have h2 : Entails.eval a c7618 := derived7618 a h
  have h3 : Entails.eval a c8757 := derived8757 a h
  have h4 : Entails.eval a c8758 := derived8758 a h
  have h5 : Entails.eval a c1058 := h 1057 (by decide)
  have h6 : Entails.eval a c1932 := h 1931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8760 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8755, some c8750, some c8720, some c8718, some c8759, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8760 : lratChecker f8760 p8760 = .success := by decide +kernel
theorem unsat8760 : Unsatisfiable (PosFin 65) f8760 := by
  apply lratCheckerSound f8760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8760
  · intro a ha; simp [p8760] at ha; subst a; trivial
  · exact checked8760
theorem derived8760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8760 := by
  apply localUnsat_implies_entails f8760 [c8755, c8750, c8720, c8718, c8759] c8760 unsat8760 (by rfl) a
  have h0 : Entails.eval a c8755 := derived8755 a h
  have h1 : Entails.eval a c8750 := derived8750 a h
  have h2 : Entails.eval a c8720 := derived8720 a h
  have h3 : Entails.eval a c8718 := derived8718 a h
  have h4 : Entails.eval a c8759 := derived8759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8761 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8720, some c8750, some c8755, some c8760, some c7568, some c8707, some c7492, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8761 : lratChecker f8761 p8761 = .success := by decide +kernel
theorem unsat8761 : Unsatisfiable (PosFin 65) f8761 := by
  apply lratCheckerSound f8761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8761
  · intro a ha; simp [p8761] at ha; subst a; trivial
  · exact checked8761
theorem derived8761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8761 := by
  apply localUnsat_implies_entails f8761 [c8720, c8750, c8755, c8760, c7568, c8707, c7492] c8761 unsat8761 (by rfl) a
  have h0 : Entails.eval a c8720 := derived8720 a h
  have h1 : Entails.eval a c8750 := derived8750 a h
  have h2 : Entails.eval a c8755 := derived8755 a h
  have h3 : Entails.eval a c8760 := derived8760 a h
  have h4 : Entails.eval a c7568 := derived7568 a h
  have h5 : Entails.eval a c8707 := derived8707 a h
  have h6 : Entails.eval a c7492 := derived7492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8762 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7174, some c7338, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8762 : lratChecker f8762 p8762 = .success := by decide +kernel
theorem unsat8762 : Unsatisfiable (PosFin 65) f8762 := by
  apply lratCheckerSound f8762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8762
  · intro a ha; simp [p8762] at ha; subst a; trivial
  · exact checked8762
theorem derived8762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8762 := by
  apply localUnsat_implies_entails f8762 [c7174, c7338] c8762 unsat8762 (by rfl) a
  have h0 : Entails.eval a c7174 := derived7174 a h
  have h1 : Entails.eval a c7338 := derived7338 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8763 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8723, some c8762, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8763 : lratChecker f8763 p8763 = .success := by decide +kernel
theorem unsat8763 : Unsatisfiable (PosFin 65) f8763 := by
  apply lratCheckerSound f8763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8763
  · intro a ha; simp [p8763] at ha; subst a; trivial
  · exact checked8763
theorem derived8763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8763 := by
  apply localUnsat_implies_entails f8763 [c8723, c8762] c8763 unsat8763 (by rfl) a
  have h0 : Entails.eval a c8723 := derived8723 a h
  have h1 : Entails.eval a c8762 := derived8762 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8764 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7833, some c8763, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p8764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8764 : lratChecker f8764 p8764 = .success := by decide +kernel
theorem unsat8764 : Unsatisfiable (PosFin 65) f8764 := by
  apply lratCheckerSound f8764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8764
  · intro a ha; simp [p8764] at ha; subst a; trivial
  · exact checked8764
theorem derived8764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8764 := by
  apply localUnsat_implies_entails f8764 [c7833, c8763] c8764 unsat8764 (by rfl) a
  have h0 : Entails.eval a c7833 := derived7833 a h
  have h1 : Entails.eval a c8763 := derived8763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8765 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7826, some c7649, some c8764, some c985, some c979, some c970, some c986, some c977, some c969, some c7827, some c7222, some c302, some c984, some c402, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8765 : lratChecker f8765 p8765 = .success := by decide +kernel
theorem unsat8765 : Unsatisfiable (PosFin 65) f8765 := by
  apply lratCheckerSound f8765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8765
  · intro a ha; simp [p8765] at ha; subst a; trivial
  · exact checked8765
theorem derived8765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8765 := by
  apply localUnsat_implies_entails f8765 [c7826, c7649, c8764, c985, c979, c970, c986, c977, c969, c7827, c7222, c302, c984, c402] c8765 unsat8765 (by rfl) a
  have h0 : Entails.eval a c7826 := derived7826 a h
  have h1 : Entails.eval a c7649 := derived7649 a h
  have h2 : Entails.eval a c8764 := derived8764 a h
  have h3 : Entails.eval a c985 := h 984 (by decide)
  have h4 : Entails.eval a c979 := h 978 (by decide)
  have h5 : Entails.eval a c970 := h 969 (by decide)
  have h6 : Entails.eval a c986 := h 985 (by decide)
  have h7 : Entails.eval a c977 := h 976 (by decide)
  have h8 : Entails.eval a c969 := h 968 (by decide)
  have h9 : Entails.eval a c7827 := derived7827 a h
  have h10 : Entails.eval a c7222 := derived7222 a h
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c984 := h 983 (by decide)
  have h13 : Entails.eval a c402 := h 401 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8766 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c292, some c1761, some c1708, some c8730, some c1971, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8766 : lratChecker f8766 p8766 = .success := by decide +kernel
theorem unsat8766 : Unsatisfiable (PosFin 65) f8766 := by
  apply lratCheckerSound f8766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8766
  · intro a ha; simp [p8766] at ha; subst a; trivial
  · exact checked8766
theorem derived8766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8766 := by
  apply localUnsat_implies_entails f8766 [c292, c1761, c1708, c8730, c1971] c8766 unsat8766 (by rfl) a
  have h0 : Entails.eval a c292 := h 291 (by decide)
  have h1 : Entails.eval a c1761 := h 1760 (by decide)
  have h2 : Entails.eval a c1708 := h 1707 (by decide)
  have h3 : Entails.eval a c8730 := derived8730 a h
  have h4 : Entails.eval a c1971 := h 1970 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8767 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8766, some c1058, some c2043, some c1932, some c1394, some c2643, some c1022, some c2469, some c2482, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8767 : lratChecker f8767 p8767 = .success := by decide +kernel
theorem unsat8767 : Unsatisfiable (PosFin 65) f8767 := by
  apply lratCheckerSound f8767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8767
  · intro a ha; simp [p8767] at ha; subst a; trivial
  · exact checked8767
theorem derived8767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8767 := by
  apply localUnsat_implies_entails f8767 [c8766, c1058, c2043, c1932, c1394, c2643, c1022, c2469, c2482] c8767 unsat8767 (by rfl) a
  have h0 : Entails.eval a c8766 := derived8766 a h
  have h1 : Entails.eval a c1058 := h 1057 (by decide)
  have h2 : Entails.eval a c2043 := h 2042 (by decide)
  have h3 : Entails.eval a c1932 := h 1931 (by decide)
  have h4 : Entails.eval a c1394 := h 1393 (by decide)
  have h5 : Entails.eval a c2643 := h 2642 (by decide)
  have h6 : Entails.eval a c1022 := h 1021 (by decide)
  have h7 : Entails.eval a c2469 := h 2468 (by decide)
  have h8 : Entails.eval a c2482 := h 2481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8768 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c417, some c403, some c381, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8768 : lratChecker f8768 p8768 = .success := by decide +kernel
theorem unsat8768 : Unsatisfiable (PosFin 65) f8768 := by
  apply lratCheckerSound f8768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8768
  · intro a ha; simp [p8768] at ha; subst a; trivial
  · exact checked8768
theorem derived8768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8768 := by
  apply localUnsat_implies_entails f8768 [c417, c403, c381] c8768 unsat8768 (by rfl) a
  have h0 : Entails.eval a c417 := h 416 (by decide)
  have h1 : Entails.eval a c403 := h 402 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8769 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7649, some c8768, some c8764, some c7826, some c7845, some c8765, some c7827, some c8767, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8769 : lratChecker f8769 p8769 = .success := by decide +kernel
theorem unsat8769 : Unsatisfiable (PosFin 65) f8769 := by
  apply lratCheckerSound f8769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8769
  · intro a ha; simp [p8769] at ha; subst a; trivial
  · exact checked8769
theorem derived8769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8769 := by
  apply localUnsat_implies_entails f8769 [c7649, c8768, c8764, c7826, c7845, c8765, c7827, c8767] c8769 unsat8769 (by rfl) a
  have h0 : Entails.eval a c7649 := derived7649 a h
  have h1 : Entails.eval a c8768 := derived8768 a h
  have h2 : Entails.eval a c8764 := derived8764 a h
  have h3 : Entails.eval a c7826 := derived7826 a h
  have h4 : Entails.eval a c7845 := derived7845 a h
  have h5 : Entails.eval a c8765 := derived8765 a h
  have h6 : Entails.eval a c7827 := derived7827 a h
  have h7 : Entails.eval a c8767 := derived8767 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8770 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7649, some c8764, some c8768, some c8769, some c7139, some c1802, some c1815, some c1789, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8770 : lratChecker f8770 p8770 = .success := by decide +kernel
theorem unsat8770 : Unsatisfiable (PosFin 65) f8770 := by
  apply lratCheckerSound f8770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8770
  · intro a ha; simp [p8770] at ha; subst a; trivial
  · exact checked8770
theorem derived8770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8770 := by
  apply localUnsat_implies_entails f8770 [c7649, c8764, c8768, c8769, c7139, c1802, c1815, c1789] c8770 unsat8770 (by rfl) a
  have h0 : Entails.eval a c7649 := derived7649 a h
  have h1 : Entails.eval a c8764 := derived8764 a h
  have h2 : Entails.eval a c8768 := derived8768 a h
  have h3 : Entails.eval a c8769 := derived8769 a h
  have h4 : Entails.eval a c7139 := derived7139 a h
  have h5 : Entails.eval a c1802 := h 1801 (by decide)
  have h6 : Entails.eval a c1815 := h 1814 (by decide)
  have h7 : Entails.eval a c1789 := h 1788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8771 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7649, some c8764, some c8770, some c293, some c7375, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8771 : lratChecker f8771 p8771 = .success := by decide +kernel
theorem unsat8771 : Unsatisfiable (PosFin 65) f8771 := by
  apply lratCheckerSound f8771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8771
  · intro a ha; simp [p8771] at ha; subst a; trivial
  · exact checked8771
theorem derived8771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8771 := by
  apply localUnsat_implies_entails f8771 [c7649, c8764, c8770, c293, c7375] c8771 unsat8771 (by rfl) a
  have h0 : Entails.eval a c7649 := derived7649 a h
  have h1 : Entails.eval a c8764 := derived8764 a h
  have h2 : Entails.eval a c8770 := derived8770 a h
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c7375 := derived7375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8772 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8761, some c8742, some c8771, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8772 : lratChecker f8772 p8772 = .success := by decide +kernel
theorem unsat8772 : Unsatisfiable (PosFin 65) f8772 := by
  apply lratCheckerSound f8772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8772
  · intro a ha; simp [p8772] at ha; subst a; trivial
  · exact checked8772
theorem derived8772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8772 := by
  apply localUnsat_implies_entails f8772 [c8761, c8742, c8771] c8772 unsat8772 (by rfl) a
  have h0 : Entails.eval a c8761 := derived8761 a h
  have h1 : Entails.eval a c8742 := derived8742 a h
  have h2 : Entails.eval a c8771 := derived8771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8773 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7466, some c7847, some c7825, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8773 : lratChecker f8773 p8773 = .success := by decide +kernel
theorem unsat8773 : Unsatisfiable (PosFin 65) f8773 := by
  apply lratCheckerSound f8773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8773
  · intro a ha; simp [p8773] at ha; subst a; trivial
  · exact checked8773
theorem derived8773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8773 := by
  apply localUnsat_implies_entails f8773 [c7466, c7847, c7825] c8773 unsat8773 (by rfl) a
  have h0 : Entails.eval a c7466 := derived7466 a h
  have h1 : Entails.eval a c7847 := derived7847 a h
  have h2 : Entails.eval a c7825 := derived7825 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8774 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8773, some c7847, some c7845, some c7753, some c7819, some c7836, some c7827, some c739, some c729, some c736, some c742, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8774 : lratChecker f8774 p8774 = .success := by decide +kernel
theorem unsat8774 : Unsatisfiable (PosFin 65) f8774 := by
  apply lratCheckerSound f8774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8774
  · intro a ha; simp [p8774] at ha; subst a; trivial
  · exact checked8774
theorem derived8774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8774 := by
  apply localUnsat_implies_entails f8774 [c8773, c7847, c7845, c7753, c7819, c7836, c7827, c739, c729, c736, c742] c8774 unsat8774 (by rfl) a
  have h0 : Entails.eval a c8773 := derived8773 a h
  have h1 : Entails.eval a c7847 := derived7847 a h
  have h2 : Entails.eval a c7845 := derived7845 a h
  have h3 : Entails.eval a c7753 := derived7753 a h
  have h4 : Entails.eval a c7819 := derived7819 a h
  have h5 : Entails.eval a c7836 := derived7836 a h
  have h6 : Entails.eval a c7827 := derived7827 a h
  have h7 : Entails.eval a c739 := h 738 (by decide)
  have h8 : Entails.eval a c729 := h 728 (by decide)
  have h9 : Entails.eval a c736 := h 735 (by decide)
  have h10 : Entails.eval a c742 := h 741 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8775 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8774, some c7467, some c7469, some c7394, some c7382, some c1438, some c1759, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8775 : lratChecker f8775 p8775 = .success := by decide +kernel
theorem unsat8775 : Unsatisfiable (PosFin 65) f8775 := by
  apply lratCheckerSound f8775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8775
  · intro a ha; simp [p8775] at ha; subst a; trivial
  · exact checked8775
theorem derived8775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8775 := by
  apply localUnsat_implies_entails f8775 [c8774, c7467, c7469, c7394, c7382, c1438, c1759] c8775 unsat8775 (by rfl) a
  have h0 : Entails.eval a c8774 := derived8774 a h
  have h1 : Entails.eval a c7467 := derived7467 a h
  have h2 : Entails.eval a c7469 := derived7469 a h
  have h3 : Entails.eval a c7394 := derived7394 a h
  have h4 : Entails.eval a c7382 := derived7382 a h
  have h5 : Entails.eval a c1438 := h 1437 (by decide)
  have h6 : Entails.eval a c1759 := h 1758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8776 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7549, some c7617, some c7625, some c1351, some c1967, some c7623, some c1310, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8776 : lratChecker f8776 p8776 = .success := by decide +kernel
theorem unsat8776 : Unsatisfiable (PosFin 65) f8776 := by
  apply lratCheckerSound f8776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8776
  · intro a ha; simp [p8776] at ha; subst a; trivial
  · exact checked8776
theorem derived8776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8776 := by
  apply localUnsat_implies_entails f8776 [c7549, c7617, c7625, c1351, c1967, c7623, c1310] c8776 unsat8776 (by rfl) a
  have h0 : Entails.eval a c7549 := derived7549 a h
  have h1 : Entails.eval a c7617 := derived7617 a h
  have h2 : Entails.eval a c7625 := derived7625 a h
  have h3 : Entails.eval a c1351 := h 1350 (by decide)
  have h4 : Entails.eval a c1967 := h 1966 (by decide)
  have h5 : Entails.eval a c7623 := derived7623 a h
  have h6 : Entails.eval a c1310 := h 1309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8777 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7424, some c7621, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p8777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8777 : lratChecker f8777 p8777 = .success := by decide +kernel
theorem unsat8777 : Unsatisfiable (PosFin 65) f8777 := by
  apply lratCheckerSound f8777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8777
  · intro a ha; simp [p8777] at ha; subst a; trivial
  · exact checked8777
theorem derived8777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8777 := by
  apply localUnsat_implies_entails f8777 [c7424, c7621] c8777 unsat8777 (by rfl) a
  have h0 : Entails.eval a c7424 := derived7424 a h
  have h1 : Entails.eval a c7621 := derived7621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8778 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7425, some c7547, some c7316, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8778 : lratChecker f8778 p8778 = .success := by decide +kernel
theorem unsat8778 : Unsatisfiable (PosFin 65) f8778 := by
  apply lratCheckerSound f8778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8778
  · intro a ha; simp [p8778] at ha; subst a; trivial
  · exact checked8778
theorem derived8778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8778 := by
  apply localUnsat_implies_entails f8778 [c7425, c7547, c7316] c8778 unsat8778 (by rfl) a
  have h0 : Entails.eval a c7425 := derived7425 a h
  have h1 : Entails.eval a c7547 := derived7547 a h
  have h2 : Entails.eval a c7316 := derived7316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8779 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8776, some c7394, some c8777, some c8778, some c7457, some c7316, some c7620, some c7624, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p8779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8779 : lratChecker f8779 p8779 = .success := by decide +kernel
theorem unsat8779 : Unsatisfiable (PosFin 65) f8779 := by
  apply lratCheckerSound f8779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8779
  · intro a ha; simp [p8779] at ha; subst a; trivial
  · exact checked8779
theorem derived8779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8779 := by
  apply localUnsat_implies_entails f8779 [c8776, c7394, c8777, c8778, c7457, c7316, c7620, c7624] c8779 unsat8779 (by rfl) a
  have h0 : Entails.eval a c8776 := derived8776 a h
  have h1 : Entails.eval a c7394 := derived7394 a h
  have h2 : Entails.eval a c8777 := derived8777 a h
  have h3 : Entails.eval a c8778 := derived8778 a h
  have h4 : Entails.eval a c7457 := derived7457 a h
  have h5 : Entails.eval a c7316 := derived7316 a h
  have h6 : Entails.eval a c7620 := derived7620 a h
  have h7 : Entails.eval a c7624 := derived7624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8780 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8775, some c8779, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8780 : lratChecker f8780 p8780 = .success := by decide +kernel
theorem unsat8780 : Unsatisfiable (PosFin 65) f8780 := by
  apply lratCheckerSound f8780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8780
  · intro a ha; simp [p8780] at ha; subst a; trivial
  · exact checked8780
theorem derived8780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8780 := by
  apply localUnsat_implies_entails f8780 [c8775, c8779] c8780 unsat8780 (by rfl) a
  have h0 : Entails.eval a c8775 := derived8775 a h
  have h1 : Entails.eval a c8779 := derived8779 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived8780

end CochromaticTwenty.Certificates.FixedCore1
